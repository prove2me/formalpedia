-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalCompensatedL1DifferenceBound
-- name    : Kyprianou.Ch04.physicalCompensatedL1DifferenceBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:02.928998+00:00
-- url     : https://prove2.me/theorems/63342eee-04bb-5289-adff-e5dc91bc39b0
-- title:
--   Physical compensated integral L1 continuity bound
-- statement:
--   Under integrability of physical raw and reference integrals and equality of expected absolute variations, the expected absolute difference of two compensated integrals is at most twice the expected reference absolute difference.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; signed physical integral convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.physicalCompensatedL1DifferenceBound
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure A) (μ : Measure A)
    (f g : Ω → A → ℝ)
    (hfM : ∀ᵐ ω ∂P, Integrable (f ω) (M ω))
    (hgM : ∀ᵐ ω ∂P, Integrable (g ω) (M ω))
    (hfμ : ∀ᵐ ω ∂P, Integrable (f ω) μ)
    (hgμ : ∀ᵐ ω ∂P, Integrable (g ω) μ)
    (R C I : Ω → ℝ)
    (hR : R =ᵐ[P] fun ω => ∫ x, |f ω x - g ω x| ∂M ω)
    (hC : C =ᵐ[P] fun ω => ∫ x, |f ω x - g ω x| ∂μ)
    (hI : I =ᵐ[P] fun ω =>
      ((∫ x, f ω x ∂M ω) - ∫ x, f ω x ∂μ) -
      ((∫ x, g ω x ∂M ω) - ∫ x, g ω x ∂μ))
    (hIm : AEStronglyMeasurable I P)
    (hRi : Integrable R P) (hCi : Integrable C P)
    (hBalance : (∫ ω, R ω ∂P) = ∫ ω, C ω ∂P) :
    Integrable I P ∧ (∫ ω, |I ω| ∂P) ≤ 2 * ∫ ω, C ω ∂P := by
  sorry
