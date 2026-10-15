-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formalJet_coefficients_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_formalJet_coefficients_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T22:37:08.634412+00:00
-- url     : https://prove2.me/theorems/6db8611d-d8d0-4d8e-93f7-8d6e90d018b8
-- title:
--   Finite interpolation of formal logarithmic jet coefficients
-- statement:
--   Every assignment to finitely many logarithmic jet coefficient requests is realized by a polynomial, provided requests have distinct label-degree pairs and distinct labels represent distinct centers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_formalJet_coefficients_surjective
    {ι α : Type} [Fintype α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k) :
    Function.Surjective (fun P : MvPolynomial (Fin (m + 1)) ℂ =>
      fun a : α => MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm (degree a))
        (formalJet (center (slot a)) P)) := by sorry
