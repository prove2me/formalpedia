-- Prove2me | Theorems.Thm_Nintendo_zelda_np
-- name    : Nintendo.zelda_np
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T11:07:16.612788+00:00
-- url     : https://prove2.me/theorems/a49df6d5-c6aa-4206-9599-34c8053ada0e
-- title:
--   The Legend of Zelda is NP-hard: with or without the hookshot
-- statement:
--   Theorems 5.1-5.2 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): deciding whether a level of The Legend of Zelda is solvable is NP-hard whether or not the player has the hookshot. The statement is two-pronged: the explicit-level 3-SAT hardness predicate holds for the Zelda level family of the worlds layer with the hookshot withheld from the level, and equally with the hookshot provided. In each prong there is a constant such that every 3-CNF formula has a level of the family whose size is at most the constant times the square of the formula's size and which is solvable exactly when the formula is satisfiable. The gadgets are the game's own mechanics: the pushed blocks, the gates toggled by switch tiles, the killing pits — and, in the hookshot prong, the beam that lands up to seven cells away on the cell before a chest, block, wall, or closed gate.
--
--   **Formalization Note** The two prongs are formed by modifying only the level's hookshot flag; the level family is otherwise the same, and the predicate is `LevelHard3Sat` in both prongs. The size is the level-extent square.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 5 (Theorems 5.1-5.2).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorems 5.1-5.2 of the paper: the Legend of Zelda is NP-hard, with or without the hookshot. -/
theorem zelda_np :
    (LevelHard3Sat (fun L : ZeldaLevel => zeldaGame {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaStart {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaGoal {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaLevelSize {L with hasHookshot := false})) ∧
    (LevelHard3Sat (fun L : ZeldaLevel => zeldaGame {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaStart {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaGoal {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaLevelSize {L with hasHookshot := true})) := by sorry

end Nintendo
