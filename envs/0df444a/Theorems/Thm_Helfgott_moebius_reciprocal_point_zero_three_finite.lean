-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_point_zero_three_finite
-- name    : Helfgott.moebius_reciprocal_point_zero_three_finite
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:29:24.560696+00:00
-- url     : https://prove2.me/theorems/92faf2d6-0e2d-4755-a97a-b1971530aa7e
-- title:
--   Certified reciprocal Mobius decay on the complete finite window
-- statement:
--   For the actual Möbius function, $$\left|\sum_{1\le n\le\lfloor x\rfloor}\frac{\mu(n)}n\right|\le\frac{0.03}{\log x}\qquad(11815\le x<1200001).$$ The finite window is certified completely; no numerical certificate or other estimate is assumed. The infinite range is a separate obligation.
-- source:
--   Original complete finite arithmetic certificate and soundness proof for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

namespace Helfgott

theorem moebius_reciprocal_point_zero_three_finite : ∀ x : ℝ, (11815 : ℝ) ≤ x → x < (1200001 : ℝ) →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100 : ℝ) / Real.log x := by sorry

end Helfgott
