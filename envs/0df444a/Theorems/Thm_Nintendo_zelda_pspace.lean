-- Prove2me | Theorems.Thm_Nintendo_zelda_pspace
-- name    : Nintendo.zelda_pspace
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T11:07:55.218603+00:00
-- url     : https://prove2.me/theorems/dd2034af-a28c-4392-aa4a-b5a8fa6c11d2
-- title:
--   A Link to the Past is PSPACE-hard: gates, switches, and teleporters
-- statement:
--   Theorem 5.5 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): deciding whether a level of Zelda: A Link to the Past is solvable is PSPACE-hard. The construction uses the gates, switches, and teleporters characteristic of the game to implement the door system of the TQBF framework. The formal statement is the explicit-level quantified hardness predicate over the Zelda level family: there is a constant such that every quantified formula with a 3-CNF matrix has a level of the family whose size is at most the constant times the square of the formula's size and whose goal is reachable from the start exactly when the formula is true.
--
--   **Formalization Note** The model is the Zelda world of the worlds layer — the same model as the NP milestone, the levels carrying their initial gate states and the hookshot availability unrestricted; the predicate is `LevelHardTqbf` and the size is the level-extent square.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 5 (Theorem 5.5).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorem 5.5 of the paper: Zelda, A Link to the Past is PSPACE-hard. -/
theorem zelda_pspace :
    LevelHardTqbf zeldaGame zeldaStart zeldaGoal zeldaLevelSize := by sorry

end Nintendo
