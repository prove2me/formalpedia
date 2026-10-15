-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T23:19:24.511384+00:00
-- url     : https://prove2.me/theorems/8bbefc4a-0c6a-4ecc-9ff7-8285e72ff911
-- title:
--   Surjectivity of finite logarithmic jet coefficient interpolation
-- statement:
--   For a finite family of requests with distinct slot-degree pairs and distinct centers, a polynomial realizes any prescribed complex values at all the requested formal logarithmic jet coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (value : α → ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) = value b := by sorry
