-- Prove2me | Theorems.Thm_JHolomorphic_integral_inv_sub_smul_eq_lsmul_convolution
-- name    : JHolomorphic.integral_inv_sub_smul_eq_lsmul_convolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T09:56:23.224328+00:00
-- url     : https://prove2.me/theorems/1019c4e4-3c88-40a4-bedb-06533269dc17
-- title:
--   The Cauchy transform as a convolution
-- statement:
--   Let $E$ be a complex normed space and $h:\mathbb C\to E$. The Cauchy transform $z\mapsto\int_{\mathbb C}(z-\zeta)^{-1}h(\zeta)\,d\zeta$ coincides, as a function, with the convolution of the kernel $t\mapsto t^{-1}$ with $h$, where the product is scalar multiplication. This identifies the transform with Mathlib's convolution so that the convolution API applies to it.
--
--   **Formalization Note** The right-hand side is `(fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] h`, with `E` viewed as a real normed space. Both sides use the Bochner integral, so they agree also where the integrals diverge (both are $0$ there).
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Convolution

/-- The Cauchy transform `z ↦ ∫ (z - ζ)⁻¹ • h ζ dζ` is the Mathlib convolution of the kernel `t ↦ t⁻¹` with `h`, taken with the real bilinear map `lsmul ℝ ℂ`. -/
theorem integral_inv_sub_smul_eq_lsmul_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (h : ℂ → E) :
    (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) =
      (fun t : ℂ => t⁻¹) ⋆[(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E), volume] h := by
  sorry

end JHolomorphic
