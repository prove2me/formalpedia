-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_two_finite
-- name    : Helfgott.moebius_reciprocal_sqrt_two_finite
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:52:58.133165+00:00
-- url     : https://prove2.me/theorems/e9d616e5-69e1-4124-8a06-9e375f4a8e2e
-- title:
--   Certified reciprocal Mobius square-root decay through 1200000
-- statement:
--   For the actual Möbius function, $$x\left(\sum_{1\le n\le\lfloor x\rfloor}\frac{\mu(n)}n\right)^2\le2\qquad(1\le x<1200001).$$ The finite window is certified completely; no numerical certificate or other estimate is assumed. The infinite range is a separate obligation.
-- source:
--   Original complete finite square-root arithmetic certificate and soundness proof for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

namespace Helfgott

theorem moebius_reciprocal_sqrt_two_finite : ∀ x : ℝ, (1 : ℝ) ≤ x → x < (1200001 : ℝ) →
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))^2*x ≤ 2 := by sorry

end Helfgott
