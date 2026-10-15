-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_jet_gluing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_jet_gluing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:14:47.268977+00:00
-- url     : https://prove2.me/theorems/bcef6f92-f0ca-46c1-88fd-93d33c07d6bd
-- title:
--   Finite formal jet gluing at distinct centers
-- statement:
--   For finitely many requested formalJet coefficients, a single polynomial can match the corresponding coefficients of prescribed local polynomials at pairwise distinct centers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_jet_gluing
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hcenters : ∀ i j, i ≠ j → ∃ k, center i k ≠ center j k)
    (Q : ι → MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) (Q (slot b))) := by sorry
