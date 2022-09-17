/*
 CP Net Solving Algorithms
 
 Notes:
 program must be compiled using c++11.  I also compile using O3 level optimization, which significantly reduces runtime
 
 g++ -std=c++11 -O3 -o main main.cpp
 ./main
 
 This is included in the Makefile
 
 This program is a collection of algorithms intended to solve a Constrained CP-Net.
 A CSP, or Constraint Satisfaction Problem, is a common problem in a wide variety of disciplines in which a collection of variables have constraints on what values they are allowed to take.  These may be unary (a constraint on a single variable, say, var A cannot equal 1), binary (if A = 1, B cannot equal 2), ternary (if A = 1 and B = 2, C cannot be 3), etc.
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
 */

#include <algorithm> //for std::find
#include <cassert>
#include <chrono>
#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <numeric> //for std::iota
#include <random>  // std::default_random_engine
#include <vector>

//typedef to improve readability
//IncompatibleTuple is a 2D array of bools, which are stored as single bits (vector<bool> is optimized)
typedef std::vector<std::vector<bool> > IncompatibleTuple;
//typedef std::map<Tuple, std::vector<Tuple> > constraintMap;

struct Variable
{
    int currentValue;
    std::vector<int> possibleValues;
    
    //new data field: parents
    //just a list of the parents
    std::vector<int> parents;
    
    //new data field: ordering
    //contains all the orderings for this variable
    //say there are 3 parents with 2 values each, there will be 8 possible combinations of values
    //index 0 represents values 0, 0, 0
    //index 1 represents values 0, 0, 1, and so on
    //the index for a specific ordering given the values of n parents is:
    //parent(n) + parent(n - 1) * (domain ^ 1) + parent(n - 2) * (domain ^ 2) + ... parent(1) * (domain ^ n-1)
    std::vector<std::vector<int> > ordering;
};

struct VariablePair
{
    int var1, var2;
};

//constraints are stored as a 2D array of pointers to tuples
std::vector<std::vector<IncompatibleTuple*>> constraintMap;

std::vector<Variable> variables;
//new data field to hold the list of pareto optimal solutions
std::vector<std::vector<int> > solutions;
int bestViolationCount;

int numberOfVars, domainSize, numberOfConstraints, incompatibleTuples, constraintMapSize, desiredSolutions;
float tightness, alpha, r;

void printSolutions();

void readValues()
{
    std::cout << "Number of variables (n): ";
    std::cin >> numberOfVars;
    std::cout << "Tightness (p): ";
    std::cin >> tightness;
    std::cout << "alpha: ";
    std::cin >> alpha;
    std::cout << "r: ";
    std::cin >> r;
    std::cout << "Number of desired pareto optimal solutions (k): ";
    std::cin >> desiredSolutions;
}

void calculateValues()
{
    //std::cout << "Calculating values\n";
    domainSize = pow(numberOfVars, alpha);
    numberOfConstraints = round(r * numberOfVars * log(numberOfVars));
    incompatibleTuples = round(tightness * domainSize * domainSize);
    constraintMapSize = numberOfVars;
}

void generateVariables()
{
    //std::cout << "Generating variables\n";
    Variable* currentVar;
    for (int i = 0; i < numberOfVars; i++)
    {
        currentVar = new Variable;
        currentVar->possibleValues.resize(domainSize);
        //fill with the values it can take, which begins with 0, 1, 2 ... n, and will be reduced later
        std::iota(currentVar->possibleValues.begin(), currentVar->possibleValues.end(), 0);
        variables.push_back(*currentVar);
    }
}

/*
 for each constraint
    pick var1
    pick var2 != var1 and var1:var2 constraint does not already exist
    for each incompatible tuple
        choose value1
        choose value2 such that value1:value2 tuple does not already exist
        push tuple to the vector of tuples
    push the (var1, var2) pair and the vector of tuples to the constraint map
    push (var2, var1) and the vector with the pairs switched to the map, since the same constraint applies in both directions (eg. (var0, var1): (value1, value2) and (var1, var0): (value2, value1) will both be added to the map)
 */
void generateConstraints()
{
    //std::cout << "Generating constraints\n";
    
    int var1, var2;
    int value1, value2;
    int count; //used to check if we've tried every possible value for value2, and need to try a new value1
    
    //using two pointers for the tuples, because var1:var2 and var2:var1 have the same constraints, just mirrored
    //so forwardTuples stores value1:value2, and backwardTuples stores value2:value1
    IncompatibleTuple* forwardTuples;
    IncompatibleTuple* backwardTuples;
    
    srand((int) time(NULL));
    
    //initialize the constraint map, which is a 2D array of pointers to tuples
    constraintMap.resize(constraintMapSize);
    for (int i = 0; i < constraintMapSize; i++)
        constraintMap[i].resize(constraintMapSize);
    
    for (int i = 0; i < numberOfConstraints; i++)
    {
        //std::cout << "Generating constraint " << i + 1 << std::endl;
        var1 = rand() % numberOfVars;
        count = 0;
        do
        {
            var2 = rand() % numberOfVars;
            count++;
            if (count > numberOfVars)
            {
                var1 = rand() % numberOfVars;
                count = 0;
            }
            //check if the pair already exists as a constraint
        } while (var1 == var2 || constraintMap[var1][var2] != nullptr);
        
        forwardTuples = new IncompatibleTuple;
        backwardTuples = new IncompatibleTuple;
        forwardTuples->resize(domainSize);
        backwardTuples->resize(domainSize);
        for (int j = 0; j < domainSize; j++)
        {
            forwardTuples->at(j).resize(domainSize);
            backwardTuples->at(j).resize(domainSize);
        }
        
        constraintMap[var1][var2] = forwardTuples;
        constraintMap[var2][var1] = backwardTuples;
        
        for (int j = 0; j < incompatibleTuples; j++)
        {
            //std::cout << "Generating tuple " << j + 1 << std::endl;
            value1 = rand() % domainSize;
            count = 0;
            do
            {
                value2 = rand() % domainSize;
                count++;
                if (count > domainSize)
                {
                    value1 = rand() % domainSize;
                    count = 0;
                }
                //std::cout << "trying value2: " << value2 << std::endl;
                //check to make sure we haven't already generated this pair (index will be true)
            } while (forwardTuples->at(value1).at(value2));
            
            //set the tuple as incompatible
            forwardTuples->at(value1).at(value2) = true;
            backwardTuples->at(value2).at(value1) = true;
        }
    }
}

/*
 generateOrdering()
 this function chooses the parents for each var and generates an ordering for each combination of parents values
 uses std::shuffle to randomize the orderings
 
 maintain a vector of all variable numbers (ie 0 to n)
 for each var i
    number of parents P = min(n * p, i)
    shuffle the first i values in the variable number vector
    assign the first P values of this shuffled vector to var[i].parents
    sort the parents vector
    resize the variable's ordering vector to be (domain ^ (#parents))
    for each entry in the ordering vector
        shuffle the variable's possibleValues vector
        assign the shuffled vector to the ordering vector entry
    
 */
void generateOrderings()
{
    int numberOfParents;
    unsigned int seed = (int) std::chrono::system_clock::now().time_since_epoch().count();
    std::vector<int> variableNumbers(numberOfVars);
    std::iota(variableNumbers.begin(), variableNumbers.end(), 0);
    
    //the first var is special because it has no parents
    //so we just shuffle the domain directly
    variables[0].ordering.resize(1);
    variables[0].ordering[0] = variables[0].possibleValues;
    std::shuffle(variables[0].ordering[0].begin(), variables[0].ordering[0].end(), std::default_random_engine(seed));
    
    //then we go through the rest of the variables, choosing parents and then generating the orderings
    for (int i = 1; i < variables.size(); i++)
    {
        numberOfParents = std::min((int)(variables.size() * tightness), i);
        variables[i].parents.resize(numberOfParents);
        seed = (int) std::chrono::system_clock::now().time_since_epoch().count();
        std::shuffle(variableNumbers.begin(), variableNumbers.begin() + i, std::default_random_engine(seed));
        std::copy(variableNumbers.begin(), variableNumbers.begin() + numberOfParents, variables[i].parents.begin());
        std::sort(variables[i].parents.begin(), variables[i].parents.end());
        
        variables[i].ordering.resize(pow(domainSize, numberOfParents));
        for (int j = 0; j < variables[i].ordering.size(); j++)
        {
            variables[i].ordering[j] = variables[i].possibleValues;
            seed = (int) std::chrono::system_clock::now().time_since_epoch().count();
            std::shuffle(variables[i].ordering[j].begin(), variables[i].ordering[j].end(), std::default_random_engine(seed));
        }
    }
}

/*
 helper function for arc consistency
 for each value of var1
    for each value of var2
        if tuple (value1, value2) does not exist (ie it is compatible)
            go to next value of var1
    if no values of var2 were accepted
        remove value from var1
 return true if at least one value was removed, false otherwise
 */
bool arcReduce(int var1, int var2)
{
    int value1, value2;
    bool valueOK;
    bool valueRemoved = false;
    
    for (int i = 0; i < variables[var1].possibleValues.size(); i++)
    {
        value1 = variables[var1].possibleValues[i];
        valueOK = false;
        for (int j = 0; j < variables[var2].possibleValues.size(); j++)
        {
            value2 = variables[var2].possibleValues[j];
            if (! (constraintMap[var1][var2]->at(value1).at(value2)))
            {
                valueOK = true;
                break;
            }
        }
        
        if (valueOK)
            continue;
        
        valueRemoved = true;
        variables[var1].possibleValues.erase(variables[var1].possibleValues.begin() + i);
        i--;
    }
    
    return valueRemoved;
}

/*
 add all constraints to a list of variable pairs
 for each arc
    run arcReduce
    if it returns true (meaning at least one value was removed from the first var)
        if var1 has empty domain
            return false, system is unsolvable
        for each incoming arc (ie constraintMap[i][var1])
            re-add the arc to the list to be checked
 */
bool runArcConsistency()
{
    std::cout << "Running arc consistency\n";
    auto start = std::chrono::high_resolution_clock::now();
    
    int var1, var2;
    VariablePair constraintArc;
    
    //first find and add all constraint arcs to be checked
    std::vector<VariablePair> arcs;
    for (int i = 0; i < constraintMapSize; i++)
        for (int j = 0; j < constraintMapSize; j++)
            if (constraintMap[i][j] != nullptr)
            {
                constraintArc.var1 = i;
                constraintArc.var2 = j;
                arcs.push_back(constraintArc);
            }
    
    //check through each arc
    for (int i = 0; i < arcs.size(); i++)
    {
        var1 = arcs[i].var1;
        var2 = arcs[i].var2;
        if (arcReduce(var1, var2))
        {
            if (variables[var1].possibleValues.empty())
                return false; //system is not arc consistent
            for (int j = 0; j < constraintMapSize; j++)
                if (j != var2 && constraintMap[j][var1] != nullptr)
                {
                    constraintArc.var1 = j;
                    constraintArc.var2 = var1;
                    arcs.push_back(constraintArc);
                }
        }
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( end - start ).count();

    std::cout << "Arc consistency took " << duration << "ms\n";
    return true;
}

/*
 helper function to see how many preferences a given solution violates
 if 0 > 2 > 1, a value of 0 violates 0 preferences, value 2 violates 1, and value 1 violates 2
 the total sum of the violations for each variable tells us how good the overall solution is
 
 violations = 0
 for each var
    get parent values
    get ordering index from parent values
    for each value in ordering
        if var's value != ordering's value
            violations++
        else
            break (go to next var)
 return violations
 */
int countViolations(std::vector<int> currentSolution)
{
    int orderingIndex, parentIndex;
    int violations = 0;
    
    for (int currentVar = 0; currentVar < numberOfVars; currentVar++)
    {
        orderingIndex = 0;
        
        //first var has no parents, so it's always the first ordering
        if (currentVar != 0)
        {
            for (int i = 0; i < variables[currentVar].parents.size(); i++)
            {
                parentIndex = variables[currentVar].parents[i];
                orderingIndex += (currentSolution[parentIndex] * (pow(domainSize, (variables[currentVar].parents.size() - 1 - i))));
            }
        }
        
        for (int i = 0; i < variables[currentVar].ordering.size(); i++)
        {
            if (currentSolution[currentVar] != variables[currentVar].ordering[orderingIndex][i])
                violations++;
            else
                break;
        }
    }
    return violations;
}

/*
 we maintain a count of the fewest number of constrait violations seen so far, ie the best solution
 if the new solution has an equal number of violations, we consider it incomparable and add it to the list
 if it has fewer violations, it dominates all other solutions seen so far, so we empty the list
 if it has more violations, we ignore it
 */
void dominanceTest()
{
    std::vector<int> currentSolution(numberOfVars);
    for (int i = 0; i < variables.size(); i++)
        currentSolution[i] = variables[i].currentValue;
    
    int currentViolations = countViolations(currentSolution);
    //std::cout << "Solution " << solutions.size() << " violations: " << currentViolations << std::endl;
    //solutions.push_back(currentSolution);
    if (currentViolations < bestViolationCount)
    {
        solutions.clear();
        solutions.push_back(currentSolution);
    }
    else if (currentViolations == bestViolationCount)
    {
        solutions.push_back(currentSolution);
    }
}

bool valueAllowed(int var, int value)
{
    for (int i = 0; i < variables[var].possibleValues.size(); i++)
    {
        if (value == variables[var].possibleValues[i])
            return true;
    }
    return false;
}

/*
 calculate ordering index for the current vars parents

 for each value of the given variable
    for each prior variable
        if constraint exists, (currentvar, previous)
            if tuple exists (current value is incompatible)
                go to next value of current variable
    if this is the last variable
        add current solution to solutions list
        do dominance testing
        go to next value of current var and continue as normal
    else
        call backtrackSubroutine(var + 1)
    if number of solutions == k
        return
    else goto next value of current var
 if there are no values left
    return
 */

void backtrackSubroutine(int currentVar)
{
    //since this routine is recursive, these variables are static to save space
    //since only one of each is ever required at a time and values within function calls don't need to be saved
    static bool incompatibilityFound;
    static IncompatibleTuple* tuplePair;
    static int value1, value2;
    static int parentIndex;
    
    int orderingIndex = 0; //non static, since we want to save the current ordering for when the next function returns
    
    //first var has no parents, so it's always the first ordering
    if (currentVar != 0)
    {
        for (int i = 0; i < variables[currentVar].parents.size(); i++)
        {
            parentIndex = variables[currentVar].parents[i];
            orderingIndex += (variables[parentIndex].currentValue * (pow(domainSize, (variables[currentVar].parents.size() - 1 - i))));
        }
    }
    
    for (int i = 0; i < variables[currentVar].ordering[orderingIndex].size(); i++)
    {
        variables[currentVar].currentValue = variables[currentVar].ordering[orderingIndex][i];
        //ensuring the selected value is actually in the domain, since the ordering domain doesn't change
        if (std::find(variables[currentVar].possibleValues.begin(), variables[currentVar].possibleValues.end(), variables[currentVar].currentValue) == variables[currentVar].possibleValues.end())
        {
            incompatibilityFound = true;
            continue;
        }
        
        incompatibilityFound = false;
        for (int previousVar = currentVar - 1; previousVar >= 0; previousVar--)
        {
            if (constraintMap[currentVar][previousVar] != nullptr)
            {
                //std::cout << "Constraint exists with var" << previousVar << std::endl;
                value1 = variables[currentVar].currentValue;
                value2 = variables[previousVar].currentValue;
                
                //check if the selected values actually form an incompatible tuple
                tuplePair = constraintMap[currentVar][previousVar];
                if (tuplePair->at(value1).at(value2))
                {
                    //std::cout << "Incompatible tuple " << value1 << "," << value2 << std::endl;
                    incompatibilityFound = true;
                    break;
                }
            }
        }
        
        if (incompatibilityFound)
        {
            //std::cout << "Incompatibility found, going to next value\n";
            continue;
        }
        
        //if we reach this point, we made it through all prior vars without a conflict on the current value
        
        //if this is the last variable and there is no conflict, check the solution
        if (currentVar == numberOfVars - 1)
        {
            dominanceTest();
        }
        else
        {
            backtrackSubroutine(currentVar + 1);
        }
        
        if (solutions.size() == desiredSolutions)
            return;
    }
    return;
}


void runStandardBacktrack()
{
    std::cout << "Running standard backtrack\n";
    auto start = std::chrono::high_resolution_clock::now();
    
    bestViolationCount = 10000;
    solutions.clear();
    
    backtrackSubroutine(0);
    if (solutions.size() == 0)
        std::cout << "No solutions found\n";
    else
    {
        std::cout << "Solution found via standard backtrack\n";
        printSolutions();
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( end - start ).count();

    std::cout << "Standard backtrack search took " << duration << "ms\n";
}

/*
 save current domains of all vars
 for each value of current var
    for each future var
        if constraint (var1, var2) exists
            for each value of var2
                if tuple (value1, value2) exists
                    remove value2 from var2 domain
                    if var2 domain is empty
                        reset domains
                        goto next value for var1
    if all future vars have successfully been forward checked
        if this is the last var
            return true
        if (forwardCheck next var)
            return true
        else
            reset domains
            go to next value for var1
 if no more values for var1
    return fail

*/
void forwardCheckSubroutine(int var1)
{
    //save the domain of all vars
    std::vector<Variable> variablesCopy = variables;
    
    static int value1, value2;
    static bool goToNextValue;
    static int parentIndex;
    
    int orderingIndex = 0; //non static, since we want to save the current ordering for when the next function returns
    
    //first var has no parents, so it's always the first ordering
    if (var1 != 0)
    {
        for (int i = 0; i < variables[var1].parents.size(); i++)
        {
            parentIndex = variables[var1].parents[i];
            orderingIndex += (variables[parentIndex].currentValue * (pow(domainSize, (variables[var1].parents.size() - 1 - i))));
        }
    }
    
    for (int i = 0; i < variables[var1].ordering[orderingIndex].size(); i++)
    {
        goToNextValue = false;
        value1 = variables[var1].ordering[orderingIndex][i];
        if (!valueAllowed(var1, value1))
        {
            goToNextValue = true;
            continue;
        }
        
        for (int var2 = var1 + 1; var2 < numberOfVars; var2++)
        {
            if (constraintMap[var1][var2] != nullptr)
            {
                for (int j = 0; j < variables[var2].possibleValues.size(); j++)
                {
                    value2 = variables[var2].possibleValues[j];
                    if (constraintMap[var1][var2]->at(value1).at(value2))
                    {
                        variables[var2].possibleValues.erase(variables[var2].possibleValues.begin() + j);
                        j--; //since we erased a value, the next value has been moved up one location
                        if (variables[var2].possibleValues.empty())
                        {
                            //reset domain
                            variables = variablesCopy;
                            goToNextValue = true;
                            break;
                        }
                    }
                }
                if (goToNextValue)
                    break;
            }
        }
        
        if (goToNextValue)
            continue;
        
        variables[var1].currentValue = value1;
        if (var1 == numberOfVars - 1)
            dominanceTest();
        else
            forwardCheckSubroutine(var1 + 1);
        
        if (solutions.size() == desiredSolutions)
            return;
        
        variables = variablesCopy;
    }
    
    //if no value was accepted, backtrack
    return;
}

void runForwardCheck()
{
    std::cout << "Running forward check\n";
    
    auto start = std::chrono::high_resolution_clock::now();
    
    bestViolationCount = 10000;
    solutions.clear();
    
    forwardCheckSubroutine(0);
    if (solutions.size() != 0)
    {
        std::cout << "Solution found via forward checking\n";
        printSolutions();
    }
    else
    {
        std::cout << "No solution found\n";
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( end - start ).count();

    std::cout << "Forward check search took " << duration << "ms\n";
}

/*
 first part is the same as forward checking,
 since we only need to do arc consistency in one direction for the current var
 then we add on doing arc consistency in both directions for all future vars
 
 save domains
 for each value of var1
    for each future var
        if constraint (var1, var2) exists
            for each value of var2
                if (value1, value2) tuple exists
                    remove value2 from var2
                    if var2 domain is empty
                        reset domain
                        go to next value of var1
    for each future var i
        for each future var i+1
            if constraint (i, i+1) exists
                for each value of var i
                    for each value of var i+1
                        if tuple (valuei, valuei+1) does not exist
                            go to next value of var i
                    if no values were accepted (all tuples exist)
                        remove value from var i
                        if vari domain is empty
                            reset domains
                            go to next value of var1
                for each value of vari+1
                    for each value of vari
                        if tuple (vari+1, vari) does not exist
                            go to next value of var i+1
                    if no values were accepted (all tuples exist)
                        remove value from var i+1
                        if vari+1 domain is empty
                            reset domains
                            go to next value of var1
    if all future vars successfully forward checked
        if this is the last var
            return true
        if fullLookaheadSubroutine(next var)
            return true
        else
            reset domain
            go to next value of var1
if no value for var1 was accepted
    return false
 */
void fullLookaheadSubroutine(int var1)
{
    //save the domain of all vars
    std::vector<Variable> variablesCopy = variables;
    
    static int value1, value2, futureVar1, futureVar2, futureValue1, futureValue2;
    static bool goToNextValue;
    static int parentIndex;
    
    int orderingIndex = 0; //non static, since we want to save the current ordering for when the next function returns
    
    //first var has no parents, so it's always the first ordering
    if (var1 != 0)
    {
        for (int i = 0; i < variables[var1].parents.size(); i++)
        {
            parentIndex = variables[var1].parents[i];
            orderingIndex += (variables[parentIndex].currentValue * (pow(domainSize, (variables[var1].parents.size() - 1 - i))));
        }
    }
    
    //std::cout << "order: " << orderingIndex << std::endl;
    
    for (int i = 0; i < variables[var1].ordering[orderingIndex].size(); i++)
    {
        goToNextValue = false;
        value1 = variables[var1].ordering[orderingIndex][i];
        if (!valueAllowed(var1, value1))
        {
            //std::cout << "value not allowed\n";
            goToNextValue = true;
            continue;
        }
        
        //first section is just regular forward checking
        for (int var2 = var1 + 1; var2 < numberOfVars; var2++)
        {
            if (constraintMap[var1][var2] != nullptr)
            {
                //std::cout << "Constraint between var" << var1 << " and var" << var2 << std::endl;
                for (int j = 0; j < variables[var2].possibleValues.size(); j++)
                {
                    value2 = variables[var2].possibleValues[j];
                    //std::cout << "checking var" << var2 << ": " << value2 << std::endl;
                    if (constraintMap[var1][var2]->at(value1).at(value2))
                    {
                        variables[var2].possibleValues.erase(variables[var2].possibleValues.begin() + j);
                        j--;
                        //std::cout << "Erasing value from var" << var2 << std::endl;
                        if (variables[var2].possibleValues.empty())
                        {
                            //reset domain
                            variables = variablesCopy;
                            goToNextValue = true;
                            //std::cout << "Empty domain, resetting\n";
                            break;
                        }
                    }
                }
                if (goToNextValue)
                    break;
            }
        }
        
        if (goToNextValue)
            continue;
        
        //std::cout << "Forward check succeeded, doing full lookahead\n";
        //if we successfully forward checked all future vars against the current,
        //we now do full lookahead by comparing all future vars to each other
        for (futureVar1 = var1 + 1; futureVar1 < numberOfVars; futureVar1++)
        {
            for (futureVar2 = futureVar1 + 1; futureVar2 < numberOfVars; futureVar2++)
            {
                if (constraintMap[futureVar1][futureVar2] != nullptr)
                {
                    //std::cout << "constraint between var" << futureVar1 << " and var" << futureVar2 << std::endl;
                    for (int j = 0; j < variables[futureVar1].possibleValues.size(); j++)
                    {
                        goToNextValue = false;
                        futureValue1 = variables[futureVar1].possibleValues[j];
                        //std::cout << "Checking var" << futureVar1 << ": " << futureValue1 << std::endl;
                        for (int k = 0; k < variables[futureVar2].possibleValues.size(); k++)
                        {
                            futureValue2 = variables[futureVar2].possibleValues[k];
                            //std::cout << "Checking var" << futureVar2 << ": " << futureValue2 << std::endl;
                            //if tuple doesn't exist, skip to the next value for futureVar1
                            if (!constraintMap[futureVar1][futureVar2]->at(futureValue1).at(futureValue2))
                            {
                                //std::cout << "Compatible tuple, going to next value\n";
                                goToNextValue = true;
                                break;
                            }
                        }
                        if (goToNextValue)
                        {
                            //std::cout << "Going to next value\n";
                            goToNextValue = false;
                            continue;
                        }
                        
                        //std::cout << "Erasing " << futureValue1 << " from var" << futureVar1 << std::endl;
                        //if we reach this point, no value for futureVar2 was accepted
                        //so erase the current value of futureVar1 and go to the next value
                        variables[futureVar1].possibleValues.erase(variables[futureVar1].possibleValues.begin() + j);
                        j--;
                        if (variables[futureVar1].possibleValues.empty())
                        {
                            //std::cout << "Empty domain, resetting\n";
                            //reset domains
                            variables = variablesCopy;
                            goToNextValue = true;
                            break;
                        }
                    }
                    
                    //if we got an empty domain for futureVar2, need to break out and go to the next value for var1
                    if (variables[futureVar2].possibleValues.size() == 0)
                    {
                        goToNextValue = true;
                        break;
                    }
                    
                    //else, we run the same arc consistency check in the other direction
                    //we checked all values of futureVar1 to make sure they had a corresponding value for futureVar2
                    //but now we check all values of futureVar2
                    //std::cout << "Checking in reverse\n";
                    for (int j = 0; j < variables[futureVar2].possibleValues.size(); j++)
                    {
                        goToNextValue = false;
                        futureValue1 = variables[futureVar2].possibleValues[j];
                        //std::cout << "Checking var" << futureVar2 << ": " << futureValue1 << std::endl;
                        for (int k = 0; k < variables[futureVar1].possibleValues.size(); k++)
                        {
                            futureValue2 = variables[futureVar1].possibleValues[k];
                            
                            //if tuple doesn't exist, skip to the next value for futureVar1
                            if (!constraintMap[futureVar2][futureVar1]->at(futureValue1).at(futureValue2))
                            {
                                goToNextValue = true;
                                break;
                            }
                        }
                        
                        if (goToNextValue)
                        {
                            goToNextValue = false;
                            continue;
                        }
                        //if we reach this point, no value for futureVar2 was accepted
                        //so erase the current value of futureVar1 and go to the next value
                        variables[futureVar2].possibleValues.erase(variables[futureVar2].possibleValues.begin() + j);
                        j--;
                        if (variables[futureVar2].possibleValues.empty())
                        {
                            //reset domains
                            variables = variablesCopy;
                            goToNextValue = true;
                            break;
                        }
                    }
                    
                    if (goToNextValue)
                    {
                        variables = variablesCopy;
                        break;
                    }
                }
            }
            if (goToNextValue)
                break;
        }
        //if some future var had an empty domain, we need to go to the next value for var1
        if (goToNextValue)
            continue;
        
        variables[var1].currentValue = value1;
        
        if (var1 == numberOfVars - 1)
            dominanceTest();
        else
            fullLookaheadSubroutine(var1 + 1);
        
        if (solutions.size() == desiredSolutions)
            return;
        
        variables = variablesCopy;
    }
    
    //no value for var1 was accepted
    return;
}

void runFullLookahead()
{
    std::cout << "Running full lookahead\n";
    auto start = std::chrono::high_resolution_clock::now();
    
    bestViolationCount = 10000;
    solutions.clear();
    
    fullLookaheadSubroutine(0);
    if (solutions.size() != 0)
    {
        std::cout << "Solution found using full lookahead\n";
        printSolutions();
    }
    else
    {
        std::cout << "No solution found using full lookahead\n";
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( end - start ).count();

    std::cout << "Full lookahead took " << duration << "ms\n";
}

bool verifySolutions()
{
    int value1, value2;
    for (int i = 0; i < solutions.size(); i++)
    {
        for (int var1 = 0; var1 < numberOfVars; var1++)
        {
            value1 = solutions[i][var1];
            for (int var2 = var1 + 1; var2 < numberOfVars; var2++)
            {
                value2 = solutions[i][var2];
                if (constraintMap[var1][var2] != nullptr)
                {
                    if (constraintMap[var1][var2]->at(value1).at(value2))
                        return false;
                    if (constraintMap[var2][var1]->at(value2).at(value1))
                        return false;
                }
            }
        }
    }
    return true;
}

void printConstraints()
{
    std::cout << std::endl << "Constraints:\n";
    
    for (int i = 0; i < numberOfVars; i++)
    {
        for (int j = 0; j < numberOfVars; j++)
        {
            if (constraintMap[i][j] != nullptr)
            {
                std::cout << "(" << i << "," << j << "): { ";
                for (int k = 0; k < domainSize; k++)
                    for (int l = 0; l < domainSize; l++)
                        if (constraintMap[i][j]->at(k).at(l))
                            std::cout << k << "," << l << " ";
                std::cout << "}\n";
            }
        }
    }
    std::cout << std::endl;
}

void printValues()
{
    for (int i = 0; i < variables.size(); i++)
    {
        std::cout << "Var " << i << ": ";
        for (int j = 0; j < variables[i].possibleValues.size(); j++)
        {
            std::cout << variables[i].possibleValues[j] << " ";
        }
        std::cout << std::endl;
    }
}

void printOrderings()
{
    std::cout << "Orderings:\n";
    
    for (int i = 0; i < variables.size(); i++)
    {
        std::cout << "var" << i << std::endl;
        std::cout << "parents: ";
        for (int j = 0; j < variables[i].parents.size(); j++)
            std::cout << variables[i].parents[j] << " ";
        std::cout << std::endl;
        
        for (int j = 0; j < variables[i].ordering.size(); j++)
        {
            for (int k = 0; k < variables[i].ordering[j].size(); k++)
            {
                std::cout << variables[i].ordering[j][k];
                if (k != variables[i].ordering[j].size() - 1)
                std::cout << " > ";
            }
            std::cout << std::endl;
        }
        std::cout << std::endl;
    }
}

void printSolutions()
{
    std::cout << "Solution:\n";
    for (int i = 0; i < solutions.size(); i++)
    {
        std::cout << "Solution " << i + 1 << std::endl;
        for (int j = 0; j < numberOfVars; j++)
        {
            std::cout << "Var" << j << ": " << solutions[i][j] << std::endl;
        }
        std::cout << std::endl;
    }
    
}

//memory management
void cleanup()
{
    for (int i = 0; i < numberOfVars; i++)
        for (int j = 0; j < numberOfVars; j++)
            delete constraintMap[i][j];
}

int main(int argc, const char * argv[])
{
    bool solutionExists;
    int arcChoice;
    int searchChoice;
    
    readValues();
    calculateValues();
    
    generateVariables();
    generateConstraints();
    
    std::cout << "\nGenerated CSP instance:\n";
    std::cout << "Variables: " << numberOfVars << std::endl;
    std::cout << "Domain size: " << domainSize << std::endl;
    std::cout << "Constraints: " << numberOfConstraints << std::endl;
    std::cout << "Incompatible tuples: " << incompatibleTuples << std::endl;
    std::cout << "Searching for " << desiredSolutions << " pareto optimal solutions\n";
    
    printConstraints();
    
    generateOrderings();
    printOrderings();
    
    std::cout << "Do you want to run arc consistency before search algorithms? Enter 1 for yes, 0 for no\n";
    std::cin >> arcChoice;
    
    if (arcChoice == 1)
    {
        //run arc consistency
        solutionExists = runArcConsistency();
        if (!solutionExists)
            std::cout << "No solution exists\n";
        std::cout << "Search space reduced to:\n";
        printValues();
        std::cout << std::endl;
    }
    
    
    std::cout << "Do you want to run standard backtrack? Enter 1 for yes, 0 for no\n";
    std::cin >> searchChoice;
    
    if (searchChoice == 1)
    {
        runStandardBacktrack();
        std::cout << std::endl;
    }
    
    
    //save the domain of all vars before doing forward check, so that full lookahead starts from scratch
    std::vector<Variable> variablesCopy = variables;
    
    std::cout << "Do you want to run forward check? Enter 1 for yes, 0 for no\n";
    std::cin >> searchChoice;
  
    
    if (searchChoice == 1)
    {
        runForwardCheck();
        std::cout << std::endl;
    }
    
    variables = variablesCopy;
    
    std::cout << "Do you want to run full lookahead? Enter 1 for yes, 0 for no\n";
    std::cin >> searchChoice;
    

    if (searchChoice == 1)
    {
        runFullLookahead();
    }
    
    //memory management
    cleanup();
    return 0;
}
