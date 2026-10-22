-- Prove2me | Theorems.Thm_Nintendo_dkc_hard
-- name    : Nintendo.dkc_hard
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T11:06:53.541158+00:00
-- url     : https://prove2.me/theorems/25d18ce8-61e8-4f9f-8e52-72661401fcd3
-- title:
--   Donkey Kong Country is NP-hard and PSPACE-hard
-- statement:
--   Theorems 4.1-4.4 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): deciding whether a level of Donkey Kong Country is solvable is NP-hard and PSPACE-hard. The statement is a conjunction of the two explicit-level hardness predicates over the Donkey Kong Country level family of the worlds layer. First, there is a constant such that every 3-CNF formula has a level whose size is at most the constant times the square of the formula's size and which is solvable — some goal configuration reached alive from the start — exactly when the formula is satisfiable. Second, the same shape holds for quantified Boolean formulas with 3-CNF matrices and truth. The gadgets live in the game's own mechanics: barrels picked up from piles and thrown at the zingers in the row below, cannons that carry the Kong to their destinations, and the platforming moves between them.
--
--   **Formalization Note** The levels are levels of the worlds-layer Donkey Kong Country model, the Kong occupying a single cell; the two conjuncts are `LevelHard3Sat` and `LevelHardTqbf` over the same level family, and the size is the level-extent square.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 4 (Theorems 4.1-4.4).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorems 4.1-4.4 of the paper: Donkey Kong Country is NP-hard and PSPACE-hard. -/
theorem dkc_hard :
    LevelHard3Sat dkcGame dkcStart dkcGoal dkcLevelSize ∧
      LevelHardTqbf dkcGame dkcStart dkcGoal dkcLevelSize := by sorry

end Nintendo
