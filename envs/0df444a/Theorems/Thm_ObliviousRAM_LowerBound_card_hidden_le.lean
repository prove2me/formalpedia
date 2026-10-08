-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_card_hidden_le
-- name    : ObliviousRAM.LowerBound.card_hidden_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:26.692278+00:00
-- url     : https://prove2.me/theorems/1d2aa85b-6e4b-4a5c-9cd6-f2ffc6e8091a
-- title:
--   §6, p. 470 — at most (b + 2)^q legal hidden sequences
-- statement:
--   Fix a hand capacity $b$ and a visible sequence $V$ of $q$ accessed cells. Let $H$ range over hidden choices that, paired with $V$, form a legal action sequence from the game's initial state. Then
--
--   $$
--   |\{H:(V,H)\text{ is legal}\}|\le (b+2)^q.
--   $$
--
--   At each access, the hidden choice is to take, do nothing, or place one of at most $b$ held balls. This bounds the number of action histories compatible with one visible pattern.
--
--   **Formalization Note** Hidden sequences are functions on a finite index type, and the count filters for legal runs. `Hidden m` includes a placement constructor for every ball, but legality restricts it to the balls currently held.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 470, §6, proof of THEOREM 6.1, hidden-action observation; https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound
open Classical

theorem card_hidden_le {b m : ℕ} (V : List (Fin m)) :
    (Finset.univ.filter fun H : Fin V.length → Hidden m =>
      Legal b (List.ofFn fun i => (V.get i, H i))).card ≤ (b + 2) ^ V.length := by sorry

end ObliviousRAM.LowerBound
