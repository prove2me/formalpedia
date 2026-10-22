-- Prove2me | Theorems.Thm_Nintendo_mario_np
-- name    : Nintendo.mario_np
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T11:09:51.958791+00:00
-- url     : https://prove2.me/theorems/99ceac23-00a5-4812-831e-0cfcd8171ed1
-- title:
--   Super Mario Bros. is NP-hard
-- statement:
--   Theorems 3.1-3.2 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160), the paper's opening result and the goal of this mission: deciding whether a level of Super Mario Bros. is solvable is NP-hard. The formal statement is the explicit-level 3-SAT hardness predicate over the Mario level family of the worlds layer: there is a constant such that every 3-CNF formula has a level whose size is at most the constant times the square of the formula's size and which is solvable — the player reaching the level's goal alive from the start — exactly when the formula is satisfiable. The gadgets are built from the platforming engine: the jump of bounded height with at most one cell of horizontal drift, the one-way fall-through of the model's tiles, and the blocks, bricks, firebars, and goombas of the world model.
--
--   **Formalization Note** The levels are levels of the worlds-layer Mario model — the player small or big and invulnerable under a permanent star, occupying one cell when small and two when big; the predicate is `LevelHard3Sat` and the size is the level-extent square. This is the goal statement of the mission.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 3 (Theorems 3.1-3.2).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorems 3.1-3.2 of the paper: Super Mario Bros. is NP-hard. This is the goal of the mission. -/
theorem mario_np :
    LevelHard3Sat marioGame marioStart marioGoal marioLevelSize := by sorry

end Nintendo
