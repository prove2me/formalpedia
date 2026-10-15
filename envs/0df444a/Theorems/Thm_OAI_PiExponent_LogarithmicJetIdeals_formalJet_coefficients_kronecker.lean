-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_kronecker
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_kronecker
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T23:03:55.09617+00:00
-- url     : https://prove2.me/theorems/833bb3da-5aee-424a-9fb0-1800c98f2e8a
-- title:
--   Kronecker interpolation for finite logarithmic jet coefficients
-- statement:
--   For any one request in the finite family, there is a polynomial whose requested logarithmic jet coefficient is one and whose other requested coefficients are zero. Distinct requests at each center and distinct centers are ensured by the parent hypotheses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_kronecker
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (a : α) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) = if b = a then 1 else 0 := by sorry
