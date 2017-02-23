#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   bt_search.

   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice
for c in csp.get_cons_with_var(newVar):
      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''
from collections import deque

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    prune_lst = []
    # if newVar is None
    if not newVar:
        # get all constraints that only have one variable in its scope
        all_cons = filter(lambda x : len(x.get_scope())==1 and x.get_n_unasgn == 1, csp.get_all_cons())
        for c in all_cons:
            # get unassigned variable
            x = c.get_unasgn_vars()[0]
            # FCCheck will return False if it failed to satisfy this constraint by trying all possible
            # values in the domain for that unassigned variable, otherwise return True
            if(not FCCheck(c, x, prune_lst)):
                return False, prune_lst
        return True, prune_lst
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 1:
            # get unassigned variable
            x = c.get_unasgn_vars()[0]
            # FCCheck will return False if it failed to satisfy this constraint by trying all possible
            # values in the domain for that unassigned variable, otherwise return True
            if(not FCCheck(c, x, prune_lst)):
                return False, prune_lst
    return True, prune_lst

def FCCheck(c, x, prune_lst):
    vals = []
    vars = c.get_scope()
    # this is to build up the value list that can be checked upon sat_tuples
    for var in vars:
        vals.append(var.get_assigned_value())
        # find the index of the unassigned variable
        if not var.is_assigned():
            index = vars.index(var)
    for d in x.cur_domain():
        # assign this unassigned variable with different domain values
        vals[index] = d
        # check, update prune_lst and prune unsatified domain value
        if not c.check(vals):
            prune_lst.append((x, d))
            x.prune_value(d)
    # no values left in current domain, return False
    if len(x.cur_domain()) == 0:
        return False
    return True

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    # create empty queue to hold constraints
    GAC_queue = deque()
    prune_lst = []
    if not newVar:
        GAC_queue.extend(csp.get_all_cons())
    else:
        GAC_queue.extend(csp.get_cons_with_var(newVar))
    # return False if it failed in enforce_GAC method
    if(not enforce_GAC(csp, GAC_queue, prune_lst)):
        return False, prune_lst
    return True, prune_lst

def enforce_GAC(csp, GAC_queue, prune_lst):
    while(len(GAC_queue) > 0):
          # pop the earliest inserted constraint
          c = GAC_queue.popleft()
          # get the variables inside the scope
          for V in c.get_scope():
              # check every possible value inside the variable domain
              for d in V.cur_domain():
                  # try to find an assignment that satify the constraint
                  if not c.has_support(V, d):
                      V.prune_value(d)
                      prune_lst.append((V, d))
                      # if all values has been tried, clear the GAC queue and return False
                      if V.cur_domain_size() == 0:
                          GAC_queue.clear()
                          return False
                      else:
                          # push the constraints that pass the check above and is not in GAC queue into GAC queue
                          new_const = [const for const in csp.get_cons_with_var(V) if const not in GAC_queue]
                          GAC_queue.extend(new_const)
    return True
