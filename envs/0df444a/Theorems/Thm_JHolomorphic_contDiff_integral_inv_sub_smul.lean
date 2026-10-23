-- Prove2me | Theorems.Thm_JHolomorphic_contDiff_integral_inv_sub_smul
-- name    : JHolomorphic.contDiff_integral_inv_sub_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T09:01:35.949527+00:00
-- url     : https://prove2.me/theorems/d3e7cc6d-bc12-4e6a-8059-ba1a5ca4dfa2
-- title:
--   The Cauchy transform of a smooth compactly supported map solves the inhomogeneous Cauchy–Riemann equation
-- statement:
--   Let $E$ be a complex Banach space and let $h:\mathbb C\to E$ be $C^\infty$ with compact support. Then the Cauchy transform
--   $$w(z)=\int_{\mathbb C}\frac{h(\zeta)}{z-\zeta}\,d\zeta$$
--   is $C^\infty$ on $\mathbb C$ and satisfies
--   $$\partial_sw(z)+i\,\partial_tw(z)=2\pi\,h(z)\qquad(z=s+it\in\mathbb C).$$
--   Thus $\frac1{2\pi}w$ is a smooth solution of $\partial_sw+i\partial_tw=h$; this is the smooth case of the solution operator for the Cauchy–Riemann operator on the plane.
--
--   **Formalization Note** $w$ is `fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ` (complex scalar multiplication, Lebesgue measure on ℂ); $\partial_sw(z)$ and $\partial_tw(z)$ are `fderiv ℝ w z 1` and `fderiv ℝ w z Complex.I`, and the identity is `fderiv ℝ w z 1 + Complex.I • fderiv ℝ w z Complex.I = (2 * Real.pi : ℂ) • h z` for every `z`.
-- source:
--   Classical (Cauchy transform); used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Let `E` be a complex Banach space and `h : ℂ → E` smooth with compact support. Then
`w(z) = ∫ (z - ζ)⁻¹ h(ζ) dζ` is smooth and `∂ₛw + i ∂ₜw = 2π h`, where `z = s + i t`. -/
theorem contDiff_integral_inv_sub_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) ∧
      ∀ z, fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1 +
          Complex.I • fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I =
        (2 * Real.pi : ℂ) • h z := by
  sorry

end JHolomorphic
