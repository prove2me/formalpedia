-- Prove2me | Theorems.Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real
-- name    : MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/65845b47-7e09-55ab-a5a1-cfeb91913ff4
-- title:
--   Möbius change of variables on ℝ
-- statement:
--   Let $a,b,c,d$ be real numbers with $ad-bc\neq 0$, and let $G\colon\mathbb{R}\to\mathbb{C}$ be an arbitrary function (no measurability or integrability hypothesis is imposed). The assertion is the equality of Bochner integrals with respect to Lebesgue measure on $\mathbb{R}$,
--   $$\int_{\mathbb{R}}\frac{|ad-bc|}{(a+xc)^{2}}\,G\!\left(\frac{b+xd}{a+xc}\right)\,dx=\int_{\mathbb{R}}G(u)\,du,$$
--   where the real scalar $|ad-bc|/(a+xc)^{2}$ is coerced into $\mathbb{C}$ and multiplied by the value of $G$. Both integrals are the usual Bochner integrals of $\mathbb{C}$-valued functions, so each side is $0$ by convention if the corresponding integrand fails to be integrable; likewise, on the (Lebesgue-null) set where $a+xc=0$ the integrand on the left is $0$ under Lean's convention that division by zero gives zero. Thus the statement is an unconditional identity of integrals, valid for every $G$ whatsoever, rather than an identity asserted under an integrability assumption.
--
--   This is the change-of-variables formula for the action of an invertible real $2\times 2$ matrix by fractional linear substitution $x\mapsto (b+xd)/(a+xc)$, the factor $|ad-bc|/(a+xc)^{2}$ being the absolute Jacobian. It is used in the estimates for the archimedean local intertwining integrals, namely in [`AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom`](thm.html#AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by sorry
