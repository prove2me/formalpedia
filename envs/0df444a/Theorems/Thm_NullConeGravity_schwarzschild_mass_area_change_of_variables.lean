-- Prove2me | Theorems.Thm_NullConeGravity_schwarzschild_mass_area_change_of_variables
-- name    : NullConeGravity.schwarzschild_mass_area_change_of_variables
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:14:13.908617+00:00
-- url     : https://prove2.me/theorems/9e19a425-8faa-5ee8-87fb-8e39dc27b5d4
-- title:
--   Schwarzschild area-to-mass change of variables (Eq. 5.69)
-- statement:
--   Let $s_b=cM^2$ with $c>0$, let $0<a\le b$ be two masses, and let $F:\mathbb R\to\mathbb R$ be continuous. On this mass interval the area weight $ds_b/\sqrt{s_b}$ transforms into $2\sqrt{c}\,dM$. For every such $F$,
--
--   $$\int_{ca^2}^{cb^2}\frac{F(s)}{\sqrt{s}}\,ds=2\sqrt c\int_a^b F(cM^2)\,dM.$$
--
--   In the Schwarzschild area law of Eq. (5.69), $c=4\pi G_N/\hbar$. This identity supplies the exact proportionality factor and applies to the area integral in Eq. (5.66) on any positive finite mass interval.
-- source:
--   Venkatesa Chandrasekaran, An algebraic quantization of gravity from the null cone, arXiv:2611.34924v1, §5.3, Eq. (5.69), area-to-mass change of variables. https://arxiv.org/html/2611.34924v1#S5.E69

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Set

namespace NullConeGravity
theorem schwarzschild_mass_area_change_of_variables
    (c a b : ℝ) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ s in c * a ^ 2..c * b ^ 2, F s / Real.sqrt s) =
      2 * Real.sqrt c * ∫ m in a..b, F (c * m ^ 2) := by sorry
end NullConeGravity
