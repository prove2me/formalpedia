-- Prove2me | Theorems.Thm_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex
-- name    : MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/552d898e-cbe7-5924-b174-a24f06bfaed6
-- title:
--   Möbius change of variables on ℂ
-- statement:
--   Let $a,b,c,d$ be complex numbers with $ad-bc\neq0$, and let $G\colon\mathbb{C}\to\mathbb{C}$ be an arbitrary function (no measurability, continuity or integrability is assumed). Then the two Bochner integrals over $\mathbb{C}$, taken with respect to Lebesgue (area) measure on $\mathbb{C}$ viewed as a two-dimensional real vector space, satisfy $$\int_{\mathbb{C}}\frac{\|ad-bc\|^{2}}{\|a+zc\|^{4}}\,G\!\left(\frac{b+zd}{a+zc}\right)\,dz=\int_{\mathbb{C}}G(u)\,du,$$ where the real scalar $\|ad-bc\|^{2}/\|a+zc\|^{4}$ is coerced into $\mathbb{C}$ and multiplies the value of $G$. Note the substitution is $z\mapsto (b+zd)/(a+zc)$, so the roles of the entries are those of the transposed matrix. Both sides are Bochner integrals, with the usual convention that an integral of a non-integrable function is $0$; the asserted equality is therefore unconditional, the integrability of the left-hand integrand being equivalent to that of $G$. Likewise, division by zero being $0$ in Lean, the integrand is interpreted as $0$ on the (Lebesgue-null) affine set where $a+zc=0$.
--
--   This is the change-of-variables formula for a complex Möbius substitution, the Jacobian factor $|ad-bc|^{2}/|a+zc|^{4}$ being the squared modulus of the complex derivative; it records the Jacobian at a complex place occurring in archimedean intertwining integrals. It is used in the analysis of [`AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom`](thm.html#AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by sorry
