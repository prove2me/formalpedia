-- Prove2me | Theorems.Thm_JHolomorphic_integral_inv_sub_smul_dbar_eq
-- name    : JHolomorphic.integral_inv_sub_smul_dbar_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T10:52:39.672225+00:00
-- url     : https://prove2.me/theorems/99da790f-4be7-4432-b7b5-5ed92180453b
-- title:
--   Pompeiu's formula for compactly supported $C^1$ maps into a complex Banach space
-- statement:
--   Let $E$ be a complex Banach space and $h:\mathbb C\to E$ a $C^1$ map with compact support. Write $\partial_s h$, $\partial_t h$ for its partial derivatives in the real and imaginary directions. For every $z\in\mathbb C$,
--   $$\int_{\mathbb C}\frac{\partial_s h(\zeta)+i\,\partial_t h(\zeta)}{z-\zeta}\,d\zeta=2\pi\,h(z),$$
--   i.e. the Cauchy transform inverts $\partial_s+i\partial_t$ up to the factor $2\pi$ on compactly supported $C^1$ maps.
--
--   **Formalization Note** $\partial_s h(\zeta)$ and $\partial_t h(\zeta)$ are `fderiv ℝ h ζ 1` and `fderiv ℝ h ζ Complex.I`. The integrability of the integrand at $z$ is taken as a hypothesis `hint`; it always holds, the hypothesis only fixes that the Bochner integral is the genuine one.
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

/-- Vector-valued Pompeiu formula: for `h : ℂ → E` of class `C¹` with compact support, `∫ (z - ζ)⁻¹ • (∂ₛh + i ∂ₜh)(ζ) dζ = 2π h(z)`. -/
theorem integral_inv_sub_smul_dbar_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (z : ℂ)
    (hint : Integrable (fun ζ => (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I))) :
    ∫ ζ, (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I) =
      (2 * Real.pi : ℂ) • h z := by
  sorry

end JHolomorphic
