#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools

def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from
       (0,0) to (n,9)) where n can be 3 to 8.


       The input board is specified as a pair (n_grid, last_row).
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid.
       If a -1 is in the list it represents an empty cell.
       Otherwise if a number between 0--9 is in the list then this represents a
       pre-set board position. E.g., the board

       ---------------------
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists

       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]


       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.

       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each
       column.
    '''
    variable_array = []
    variable_array_4_CSP = []
    constraint_array = []
    val_range = list(range(10))
    row_nums = len(initial_tenner_board[0])
    col_nums = 10
    for row_index in range(row_nums):
        row_var = []
        vals_filled = [val for val in initial_tenner_board[0][row_index] if val != -1]
        val_domain_of_not_filled_cell = [val for val in val_range if val not in vals_filled]
        for col_index in range(col_nums):
            cell_value = initial_tenner_board[0][row_index][col_index]
            if cell_value == -1:
                row_var.append(Variable('CELL'+str(row_index)+str(col_index), val_domain_of_not_filled_cell))
            else:
                row_var.append(Variable('CELL'+str(row_index)+str(col_index), [cell_value]))
        constraint_index = 0
        for row_vars in itertools.combinations(row_var, 2):
            constraint_array.append(add_bin_comp_const(row_vars, row_index, constraint_index))
            constraint_index += 1
        variable_array.append(row_var)
        variable_array_4_CSP.extend(row_var)
    for col_index in range(col_nums):
        col_vars = [variable_array[row_index][col_index] for row_index in range(row_nums)]
        constraint_array.append(add_sum_check_cosnt(col_vars, col_index, initial_tenner_board[1][col_index]))
    for row_index in range(row_nums-1):
        for col_index in range(col_nums):
            adj_vars = []
            adj_vars.append(variable_array[row_index][col_index])
            adj_vars_1 = adj_vars + [variable_array[row_index+1][col_index]]       
            if(col_index == 0):
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index+1]]
            elif(col_index == col_nums-1):
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index-1]]
            else:
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index-1]]
                adj_vars_3 = adj_vars + [variable_array[row_index+1][col_index+1]]
            constraint_array.append(add_adj_check_cosnt(adj_vars_1, row_index, col_index, 1))
            constraint_array.append(add_adj_check_cosnt(adj_vars_2, row_index, col_index, 2))
            if 'adj_vars_3' in locals():
                constraint_array.append(add_adj_check_cosnt(adj_vars_3, row_index, col_index, 3))
    tennerCSP = CSP("Tenner_Grid", variable_array_4_CSP)
    for const in constraint_array:
        tennerCSP.add_constraint(const)
    return tennerCSP, variable_array

##############################

def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from
       (0,0) to (n,9)) where n can be 3 to 8.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.

       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular,
       model_2 has a combination of n-nary
       all-different constraints and binary not-equal constraints: all-different
       constraints for the variables in each row, binary constraints for
       contiguous cells (including diagonally contiguous cells), and n-nary sum
       constraints for each column.
       Each n-ary all-different constraint has more than two variables (some of
       these variables will have a single value in their domain).
       model_2 should create these all-different constraints between the relevant
       variables.
    '''
    variable_array = []
    variable_array_4_CSP = []
    constraint_array = []
    val_range = list(range(10))
    row_nums = len(initial_tenner_board[0])
    col_nums = 10
    for row_index in range(row_nums):
        row_var = []
        vals_filled = [val for val in initial_tenner_board[0][row_index] if val != -1]
        val_domain_of_not_filled_cell = [val for val in val_range if val not in vals_filled]
        for col_index in range(col_nums):
            cell_value = initial_tenner_board[0][row_index][col_index]
            if cell_value == -1:
                row_var.append(Variable('CELL'+str(row_index)+str(col_index), val_domain_of_not_filled_cell))
            else:
                row_var.append(Variable('CELL'+str(row_index)+str(col_index), [cell_value]))
        constraint_array.append(add_all_diff_const(row_var, row_index))
        variable_array.append(row_var)
        variable_array_4_CSP.extend(row_var)
    for col_index in range(col_nums):
        col_vars = [variable_array[row_index][col_index] for row_index in range(row_nums)]
        constraint_array.append(add_sum_check_cosnt(col_vars, col_index, initial_tenner_board[1][col_index]))
    for row_index in range(row_nums-1):
        for col_index in range(col_nums):
            adj_vars = []
            adj_vars.append(variable_array[row_index][col_index])
            adj_vars_1 = adj_vars + [variable_array[row_index+1][col_index]]       
            if(col_index == 0):
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index+1]]
            elif(col_index == col_nums-1):
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index-1]]
            else:
                adj_vars_2 = adj_vars + [variable_array[row_index+1][col_index-1]]
                adj_vars_3 = adj_vars + [variable_array[row_index+1][col_index+1]]
            constraint_array.append(add_adj_check_cosnt(adj_vars_1, row_index, col_index, 1))
            constraint_array.append(add_adj_check_cosnt(adj_vars_2, row_index, col_index, 2))
            if 'adj_vars_3' in locals():
                constraint_array.append(add_adj_check_cosnt(adj_vars_3, row_index, col_index, 3))
    tennerCSP = CSP("Tenner_Grid", variable_array_4_CSP)
    for const in constraint_array:
        tennerCSP.add_constraint(const)
    return tennerCSP, variable_array


def add_bin_comp_const(row_vars, row_index, constraint_index):
    c = Constraint('ROW'+str(row_index)+'_'+str(constraint_index), [row_vars[0], row_vars[1]])
    sat_tuples = []
    varDoms = [v.domain() for v in row_vars]
    for t in itertools.product(*varDoms):
        if t[0] != t[1]:
            sat_tuples.append(t)
    c.add_satisfying_tuples(sat_tuples)
    return c

def add_sum_check_cosnt(col_vars, col_index, sum_val):
    c = Constraint('COL'+str(col_index), col_vars)
    sat_tuples = []
    varDoms = [v.domain() for v in col_vars]
    for t in itertools.product(*varDoms):
        if sum(t) == sum_val:
            sat_tuples.append(t)
    c.add_satisfying_tuples(sat_tuples)
    return c

def add_adj_check_cosnt(adj_vars, row_index, col_index, constraint_index):
    c = Constraint('ADJ'+str(row_index)+'_'+str(col_index)+'_'+str(constraint_index), adj_vars)
    sat_tuples = []
    varDoms = [v.domain() for v in adj_vars]
    for t in itertools.product(*varDoms):
        if t[0] != t[1]:
            sat_tuples.append(t)
    c.add_satisfying_tuples(sat_tuples)
    return c

def add_all_diff_const(row_vars, row_index):
    c = Constraint('ROW'+str(row_index), row_vars)
    sat_tuples = []
    varDoms = [v.domain() for v in row_vars]
    for t in itertools.product(*varDoms):
        if len(set(t)) == len(t):
            sat_tuples.append(t)
    c.add_satisfying_tuples(sat_tuples)
    return c