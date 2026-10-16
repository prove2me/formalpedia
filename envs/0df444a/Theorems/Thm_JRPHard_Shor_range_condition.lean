-- Prove2me | Theorems.Thm_JRPHard_Shor_range_condition
-- name    : JRPHard.Shor.range_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:39:09.728735+00:00
-- url     : https://prove2.me/theorems/e38746ed-3466-4875-a0c0-3b37ea6dbb56
-- title:
--   Appendix, p. 17 — interval condition
-- statement:
--   For the Appendix endpoints $L=2^{\lambda(A-1/2)}$ and $U=2^{\lambda(A+1/2)}$, assume
--   $$2^{\lambda/2}+2^{-\lambda/2}<2\sqrt2.$$
--   Then
--   $$L+U<2\sqrt{2LU}.$$
--   This is the real numerical side condition in RangeDivisor before rounding the endpoints.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 17, Appendix, final interval claim

import Mathlib
import Definitions.Def_JRPHard_Shor_Setting

namespace JRPHard.Shor

/-- Appendix, p. 17: the two endpoints meet RangeDivisor's real inequality. -/
theorem range_condition {n : ℕ} (B : ℕ) (a : Fin n → ℕ)
    (hlam : (2 : ℝ) ^ (scale B / 2) + (2 : ℝ) ^ (-(scale B / 2)) <
      2 * Real.sqrt 2) :
    lowL B a + highU B a <
      2 * Real.sqrt (2 * lowL B a * highU B a) := by sorry

end JRPHard.Shor
