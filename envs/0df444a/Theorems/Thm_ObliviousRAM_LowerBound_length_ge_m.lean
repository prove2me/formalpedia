-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_length_ge_m
-- name    : ObliviousRAM.LowerBound.length_ge_m
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:52.265692+00:00
-- url     : https://prove2.me/theorems/f4b5be53-bb4a-4753-9860-c594a0cd81e8
-- title:
--   §6, p. 470 — the first-round lower bound of m accesses
-- statement:
--   Fix a hand capacity $b$, $m$ balls and cells, and at least one request round. Let $P$ be a correct oblivious randomized player. For any request sequence $r$ and any run $a$ that $P$ performs with positive probability on $r$,
--
--   $$
--   |a|\ge m.
--   $$
--
--   This is the first component of the access lower bound: even a run serving one particular request must cover all initially occupied cells because its visible pattern is possible for every request sequence.
--
--   **Formalization Note** Correctness holds for every positive-probability run, and obliviousness is equality of visible-pattern distributions. The at-least-one-round condition makes the first-round observation applicable.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 470, §6, proof of THEOREM 6.1, first-round observation; https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound

theorem length_ge_m {b m t : ℕ} (ht : 1 ≤ t) (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support) :
    m ≤ a.length := by sorry

end ObliviousRAM.LowerBound
