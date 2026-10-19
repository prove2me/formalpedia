-- Prove2me | Theorems.Thm_JRPHard_Shor_two_rpow_neg_le
-- name    : JRPHard.Shor.two_rpow_neg_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:37.976979+00:00
-- url     : https://prove2.me/theorems/d52acdb3-4ef8-4a9b-9de9-50c85dae444f
-- title:
--   Appendix, p. 16 — power inequality
-- statement:
--   For a real number $x$ with $0\le x\le1$, the Appendix uses
--   $$2^{-x}\le 1-\frac{x}{2}.$$
--   This estimate is one of the two elementary inequalities used to widen the prime sampling window into the multiplicative window. The companion inequality $e^x\ge1+x$ is supplied by Mathlib.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 16, Appendix, power inequality

import Mathlib

namespace JRPHard.Shor

/-- Appendix, p. 16: the stated lower exponential estimate. -/
theorem two_rpow_neg_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (2 : ℝ) ^ (-x) ≤ 1 - x / 2 := by sorry

end JRPHard.Shor
