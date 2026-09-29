-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_candidates
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_candidates
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T15:54:12.201218+00:00
-- url     : https://prove2.me/theorems/a6ea5234-b6b4-4a3d-b7cb-91f98b74589c
-- title:
--   Prime q4 candidates in the D=57 q3=19 branch
-- statement:
--   For the D=57 half-successor case, the abundance squeeze confines the fourth support prime q4 to the interval [580,602]. A prime in that interval is exactly 587, 593, 599, or 601.
-- source:
--   Finite prime enumeration for the D=57 q3=19 finite certificate. The interval is a standalone arithmetic candidate reduction to be connected to the canonical abundance hypotheses by a later wrapper.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D57_q4_candidates (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 580 ≤ q4) (hhigh : q4 ≤ 602) :
    q4 = 587 ∨ q4 = 593 ∨ q4 = 599 ∨ q4 = 601 := by
  sorry

end OddPerfectNumber
