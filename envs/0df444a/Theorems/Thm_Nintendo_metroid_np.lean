-- Prove2me | Theorems.Thm_Nintendo_metroid_np
-- name    : Nintendo.metroid_np
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T11:08:38.247115+00:00
-- url     : https://prove2.me/theorems/ccd40b48-2341-408d-bec6-10d383902861
-- title:
--   Metroid is NP-hard
-- statement:
--   Theorem 6.1 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): deciding whether a level of Metroid is solvable is NP-hard. The formal statement is the explicit-level 3-SAT hardness predicate over the Metroid level family of the worlds layer: there is a constant such that every 3-CNF formula has a level whose size is at most the constant times the square of the formula's size and which is solvable — Samus reaching the goal alive from the start — exactly when the formula is satisfiable. The gadgets are Samus's own mechanics: the morph ball and its tunnels, the beam that clears the zoomers in its path, and the platforming moves between them.
--
--   **Formalization Note** The levels are levels of the worlds-layer Metroid model, Samus occupying two cells unmorphed and one morphed, the headroom conditions that the two-cell body forces being part of what the gadget corridors must respect; the predicate is `LevelHard3Sat` and the size is the level-extent square.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 6 (Theorem 6.1).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorem 6.1 of the paper: Metroid is NP-hard. -/
theorem metroid_np :
    LevelHard3Sat metroidGame metroidStart metroidGoal metroidLevelSize := by sorry

end Nintendo
