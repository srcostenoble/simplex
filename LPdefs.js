// LPdefs.js
//
// definition of lpProblem object
// for solution of LP problems by simplex method
//
// Copyright (C) 2017 Steven R. Costenoble and Stefan Waner

// lp modes
const lp_Integral = 1;					// solve using integers?
const lp_Fraction = lp_Integral+1;		// using fractions?
const lp_Decimal = lp_Fraction+1;		// using decimals?

// lp status
const lp_no_problem = 0;				// no problem, yet
const lp_parsed = lp_no_problem+1;		// parsed a problem
const lp_phase1 = lp_parsed+1;			// done with Phase I
const lp_phase2 = lp_phase1+1;			// done with Phase II
const lp_optimal = lp_phase2+1;			// completely done - not necessarily Phase II for integer programming
const lp_no_solution = lp_optimal+1;	// no solution, don't continue

// verbosity level
const lp_verbosity_none = 0;			// how verbose should we be?
const lp_verbosity_tableaus = lp_verbosity_none + 1;		// show all tableaus
const lp_verbosity_solutions = lp_verbosity_tableaus + 1;	// tableaus and intermediate solutions

// globals
var lp_verboseLevel = lp_verbosity_none;
var lp_reportErrorsTo = "";  			// empty if default reporting, "alert" or id of	an html element
var lp_trace_string = "";				// string that will contain the tableaus, solutions, etc.

// error messages (should be reassignable by a parent container - eg in Spanish - so these are not consts)
var lp_noLPErr = "No LP problem given";
var lp_IllegCharsErr = "Illegal characters";
var lp_UnspecMaxMinErr = "Max or min not specified";
var lp_noRelationConstrErr = "Constraints must contain '=', '<=', or '>='";
var lo_tooManyTabloeausErr = "Number of tableaus exceeds ";
var lp_emptyFeasibleRegionErr = "No solution; feasible region empty";
var lp_noMaxErr = "No maximum value; the objective function can be arbitrarily large";
var lp_noMinErr = "No minimum value; the objective function can be arbitrarily large negative";
var lp_phase2TooSoonErr = "Attempting to do Phase 2 when Phase 1 is not complete.";
var lp_badExprErr = "Something's wrong in the expression ";
var lp_illegalCoeffErr = "illegal coefficient of ";
var lp_inExprErr = " in the expression\n";
var lp_objNotSetErr = "Objective not set in extractUnknowns";
var lp_noNiceSolutionErr = "No solution with the desired integer values exists"



// Setting up an lpProblem
// Do one of the following:
//   1) Supply an existing lpProblem when constructing the object
//   2) Set problemStr to a whole LP problem
//		For integer/mixed problems, add "integer x,y,z" as last line with unknowns that should be integer
//   3) Set objective to the object function, as a string of the form
//         "[max|min]inmize var = linear expression" and
//      Set constraints to an array of constraints of the form
//         "linear expr <=, >=, or = number"
//   4) Set maximize, objectiveName, unknowns, and numActualUnknowns, and
//      set tableaus to a one element array containing the first tableau
//
// Once the problem is set up, call solve().
//
// Success is indicated by this.status, which could be lp_optimal or lp_no_solution.
//
// For ordinary LP problems, solutions, including all intermediate steps, are available
// 		in this.objectiveValues and this.solutions, with tableaus in this.tableaus
//		Use the appropriate formatXXX() routine to get them nicely rounded and formatted.
//
// For integer LP problems, the actual solution is available in
// 		this.integerSolution and this.integerObjValue.
//		Use formatIntegerXXX() to get them nicely formatted.


class lpProblem
{
	constructor ( problem = null ) {
			// linear expression to optimize
		this.objective = (problem != null && typeof problem.objective == 'string') 
							? problem.objective : "";			

			// array of constraints, linear expr <=, >=, or = number
		this.constraints = (problem != null && Array.isArray(problem.constraints)) 
							? problem.constraints.slice() : [];

			// integer/mixed programming?
		this.isIntegral = (problem != null && typeof problem.isIntegral == 'boolean') 
							? problem.isIntegral : false;

			// solve using integers, fractions, or decimals?
		this.mode = (problem != null && typeof problem.mode == 'number')
							? problem.mode : lp_Decimal;

			// false for minimize
		this.maximize = (problem != null && typeof problem.maximize == 'boolean') 
							? problem.maximize : true;

			// either supplied with string problem or generated
		this.objectiveName = (problem != null && typeof problem.objectiveName == 'string') 
							? problem.objectiveName : "Obj";

			// array of names of unknowns (includes slack/surplus variables)
		this.unknowns = (problem != null && Array.isArray(problem.unknowns)) 
							? problem.unknowns.slice() : [];

			// array of unknowns for which integer values are required (mixed programming)
		this.integerUnknowns = (problem != null && Array.isArray(problem.integerUnknowns)) 
							? problem.integerUnknowns.slice() : [];
			// whether or not to show the values of the slack and surplus variables in the solution
		this.showArtificialVariables = false;
			// initial matrix of system, a la Ax >= b.
			// doesn't need to be copied, as it won't change if already filled in
		this.systemMatrix = (problem != null && Array.isArray(problem.systemMatrix))
							? problem.systemMatrix : [];

		this.systemRowIsStarred = (problem != null && Array.isArray(problem.systemRowIsStarred))
							? problem.systemRowIsStarred : [];

			// same for right hand sides of constraints
		this.constraintRHS = (problem != null && Array.isArray(problem.constraintRHS))
							? problem.constraintRHS : [];

			// similar for objective function
		this.objectiveCoeffs = (problem != null && Array.isArray(problem.objectiveCoeffs))
							? problem.objectiveCoeffs : [];

			// additional constraints used in integer programming, indexed like integerUnknowns
		this.integerMins = (problem != null && Array.isArray(problem.integerMins))
							? problem.integerMins.slice() : [];
		this.integerMaxs = (problem != null && Array.isArray(problem.integerMaxs))
							? problem.integerMaxs.slice() : [];

			// how many original unknowns?
		this.numActualUnknowns = (problem != null && typeof problem.numActualUnknowns == 'number') 
							? problem.numActualUnknowns : 0;

		this.rowIsStarred = [];			// ith entry is true if i row is starred

		this.tableaus = [];				// array of tableaus
		this.tableauDimensions = [];	// number of rows, number of columns
		this.maxNumTableaus=50;			// quite arbitrary make it a setting if associated error is thrown

		this.status = lp_no_problem;	// are we there yet?

		this.solutions = [];			// array of intermediate solutions
		this.objectiveValues = [];		// array of intermediate objective values
		this.error = "";				// error message for badly set up problem etc
		this.message = "";				// message when there is no solution for one reason or another
		
		this.integerSolution = [];		// used to return solution to integer programming problems
		this.integerObjValue = 0;
		
		this.problemStr = (problem != null && typeof problem == 'string') ? problem : "";
		
		// settings
		this.maxSigDigits = 13;			// try to push to 16 but issues with roundSigDig which internally uses three more
		this.sigDigits = 6;				// user specified for rounding of tableaus and results
		
	}
	

	// Functions
	
	solve ( ) {}								// solve it, return true if succeeded

	formatObjectiveValues ( mode = 0 ) {}			// return array of objective values, in proper form

	formatLastObjectiveValue ( mode = 0 ) {}		// same, just the last value										

											// return array of unknowns, with or w/o slack vars	
	formatUnknowns ( includeSlackVariables = false ) {}

											// use this to get the solutions, in proper form,
											// with or w/o slack vars
											// mode defaults to setting of this.mode
											// returns an array of arrays, each in order of unknowns
	formatSolutions ( includeSlackVariables = false, mode = 0 ) {}
	
											// same, but just last solution, not all intermediates
	formatLastSolution ( includeSlackVariables = false, mode = 0 ) {}

											// use these to get the integer solution when doing ILP
	formatIntegerObjectiveValue ( mode = 0) {}
	formatIntegerSolution ( includeSlackVariables = false ) {}

											// return string showing values of vars in last or integer solution,
											// using settings of showArtificialVariables & mode
	solutionToString () {}
											// same, but shows last solution, even if doing ILP
	lastSolutionToString () {}
}


// tableau class is a subclass of Array
// The 0th row and column contain labels
// The entries of the tableau itself are indexed from [1][1]
//
class tableau extends Array
{
	constructor ( arr = [] ) {			// construct from a given 2D array or tableau
		super();
		for ( var i = 0; i < arr.length; i++ )
			this[i] = arr[i].slice();
	}

	pivot ( pRow, pCol, sigDigs ) {}	// pivot, return a new tableau
	
	toString ( theMode, sigDigs ) {}	// returns an ascii formatted string representing the tableau
	
	toHTML ( theMode, sigDigs , params) {}		// returns an HTML table representing the tableau
}
