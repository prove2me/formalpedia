-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_visible_satisfies_all
-- name    : ObliviousRAM.LowerBound.visible_satisfies_all
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:01.923606+00:00
-- url     : https://prove2.me/theorems/5b3020a0-0069-429e-99e0-7e14d4708d56
-- title:
--   §6, p. 470 — every visible pattern serves every request sequence
-- statement:
--   Let $P$ be a correct oblivious randomized player for $t$ rounds and $m$ balls. If a run $a$ occurs with positive probability for one request sequence $r$, then for every other request sequence $r'$ there is a positive-probability run $a'$ of $P$ on $r'$ with the same visible cell sequence as $a$, and $a'$ satisfies $r'$:
--
--   $$
--   \forall r',\ \exists a'\in\operatorname{supp}(P(r')):\quad V(a')=V(a)\quad\text{and}\quad a'\models r'.
--   $$
--
--   This gives the common visible pattern the capacity to serve all $m^t$ possible request sequences.
--
--   **Formalization Note** The player may randomize and know the complete sequence. Obliviousness equates the full distributions of visible patterns, rather than only their supports.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 470, §6, proof of THEOREM 6.1, obliviousness observation; https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound

theorem visible_satisfies_all {b m t : ℕ} (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support)
    (r' : Fin t → Fin m) :
    ∃ a' ∈ (P.play r').support, visible a' = visible a ∧ Satisfies b a' r' := by sorry

end ObliviousRAM.LowerBound
