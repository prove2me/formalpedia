-- Prove2me | Theorems.Thm_Nintendo_fw_sat
-- name    : Nintendo.fw_sat
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T11:05:26.079215+00:00
-- url     : https://prove2.me/theorems/24f4f282-2fce-4e58-af37-5b5536a0ace8
-- title:
--   The 3-SAT framework: a level of Start, Variable, Clause, Check, and Crossover gadgets is solvable exactly when the formula is satisfiable
-- statement:
--   The 3-SAT framework of Section 2.1 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): the abstract game whose levels are built from a 3-CNF formula by the paper's Start, Variable, Clause, Check, and Crossover gadgets. The theorem states the framework's NP-hardness shape: there is a constant such that, for every 3-CNF formula, the size of the framework level built from the formula is at most the constant times the square of the formula's size, and the formula is satisfiable exactly when a goal configuration of the level is reachable from its start by the legal steps. The protocol of the level: the player sets the variables one at a time; after each choice the player may visit the clause gadgets, a visit unlocking a clause exactly when the chosen literal occurs in it, the crossover gadgets routing the paths without interference; after the last variable the player walks the check path, whose clause gates open exactly when the corresponding clause has been unlocked.
--
--   **Formalization Note** The framework level is defined in the game layer as an explicit configuration protocol (start, variable-setting, literal, check, and finish states) rather than as a grid of tiles; the crossover gadgets of the paper, whose function is to let paths cross, are embodied in the protocol's freedom to visit clause gadgets between any two variable choices. The size is the square of the numbers of variable and clause gadgets, and the hardness predicate is `Hard3Sat`.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 2.1 (after Cook 1971).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Section 2.1 of the paper: the 3-SAT framework. -/
theorem fw_sat : Hard3Sat frameworkGame fwStart fwGoal fwLevelSize := by sorry

end Nintendo
