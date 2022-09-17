# cp-net-solving-algorithms

Notes:
 program must be compiled using c++11.  I also compile using O3 level optimization, which significantly reduces runtime
 
 g++ -std=c++11 -O3 -o main main.cpp
 ./main
 
 This is included in the Makefile
 
 This program is a collection of algorithms intended to solve a Constrained CP-Net.
 A CSP, or Constraint Satisfaction Problem, is a common problem in a wide variety of disciplines in which a collection of variables have constraints on what values they are allowed to take.  
 These may be unary (a constraint on a single variable, say, var A cannot equal 1), binary (if A = 1, B cannot equal 2), ternary (if A = 1 and B = 2, C cannot be 3), etc.
 In this program, binary constraints are used, represented as tuples:
 {value1: value2} means that if var1 is value1, var2 is not allowed to be value2
 
 A CP Net, or Conditional Preferences Network, is an extension of a CSP where certain there are certain qualitative preferences on the results
 
 This program first generates a Constrained CP Net given a set of input parameters, and then attempts to find the best solutions via standard backtrack, forward checking, and full lookahead algorithms, with arc consistency optionally run beforehand
 
 It then attempts to find up to k solutions
 
 These solutions are ranked based on the number of constraints they violate.  The total ranking for the solution will be the sum of all of the order constraints it violates, and the algorithm will only keep the best (which may be up to k, if they all violate the same number of constraints)

Input parameters:
 n: number of variables
 
 p: tightness, 0 < p < 1.  Higher values mean more constraints
 
 r: 0 < r < 1.  Suggested value 0.6
 
 alpha: 0 < α < 1.  Suggested value 0.5
 
 k: number of desired solutions.  The program will stop after finding this many, but may return fewer if there are not k pareto optimal solutions
