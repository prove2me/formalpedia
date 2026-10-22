-- Prove2me | Theorems.Thm_Nintendo_pokemon_np
-- name    : Nintendo.pokemon_np
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T11:09:00.447775+00:00
-- url     : https://prove2.me/theorems/47654ab8-c65e-4921-8ab9-de868e7b79f8
-- title:
--   Pokémon is NP-hard: enemy trainers alone suffice
-- statement:
--   Theorem 7.2 of Aloupis, Demaine, Guo, and Viglietta's paper (Theoretical Computer Science 586 (2015) 135-160): deciding whether a level of Pokémon is solvable is NP-hard, and the enemy trainers alone suffice — no wild Pokémon are needed. The formal statement is the explicit-level 3-SAT hardness predicate over the Pokémon level family of the worlds layer: there is a constant such that every 3-CNF formula has a level — walls and enemy trainers only — whose size is at most the constant times the square of the formula's size and which is solvable, the player reaching the goal alive from the start, exactly when the formula is satisfiable. The gadgets are the trainers themselves: their lines of sight, blocked by walls and by other trainers' bodies, the battles that interrupt a seen step, and the luring move that draws a line-of-sight trainer to the adjacent cell, with weak trainers defeated and strong trainers killing.
--
--   **Formalization Note** The levels are levels of the worlds-layer Pokémon model with no wild encounters; the predicate is `LevelHard3Sat` and the size is the level-extent square.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 7 (Theorem 7.2).

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

namespace Nintendo

/-! Theorem 7.2 of the paper: Pokemon is NP-hard, and enemy trainers alone suffice. -/
theorem pokemon_np :
    LevelHard3Sat pokeGame pokeStart pokeGoal pokeLevelSize := by sorry

end Nintendo
