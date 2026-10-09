-- Prove2me | Theorems.Thm_GaussianMatrix_integral_power_exp_le
-- name    : GaussianMatrix.integral_power_exp_le
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:28:41.093031+00:00
-- url     : https://prove2.me/theorems/3bd44893-a196-4e2e-b604-9d4e34016f67
-- title:
--   $\int_0^t x^a e^{-x/2}\,dx\le t^{a+1}/(a+1)$ for $a>-1$, $t\ge0$
-- statement:
--   Let $a>-1$ and $t\ge0$ be real numbers. Then
--   $$\int_0^t x^{a}e^{-x/2}\,dx\;\le\;\int_0^t x^a\,dx=\frac{t^{a+1}}{a+1}.$$
--
--   This is the integration step from Tropp–Webber's (B.6) to (B.7): drop the factor $e^{-x/2}\le1$ and integrate the power. It is used with $a=(k-r-1)/2\ge-\tfrac12$.
--
--   **Formalization Note.** The left side is a lower Lebesgue integral (`lintegral`) over $(0,t]$ of `ENNReal.ofReal (x ^ a * Real.exp (-x / 2))`, and the right side is `ENNReal.ofReal (t ^ (a + 1) / (a + 1))`. Real powers are used; they are positive on $(0,t]$.
-- source:
--   standard fact: for a > −1 and t ≥ 0, ∫₀ᵗ x^a e^{−x/2} dx ≤ ∫₀ᵗ x^a dx = t^{a+1}/(a+1), since e^{−x/2} ≤ 1 for x ≥ 0. This is the integration step (B.6) ⇒ (B.7) in Tropp–Webber, arXiv:2306.12418, proof of Lemma B.3.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem integral_power_exp_le {a : ℝ} (ha : -1 < a) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by sorry

end GaussianMatrix
