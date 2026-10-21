-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement_nonpos
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_nonpos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:44:00.954206+00:00
-- url     : https://prove2.me/theorems/c8807ef3-cb4f-4b9f-bbf9-48468fc8f4f4
-- title:
--   Weighted series jets on the empty strict simplex
-- statement:
--   When H is nonpositive, positivity of the coordinate weights makes the strict weighted simplex empty. The resulting coefficient-function space is trivial, so the requested equivalence and jet identity hold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_nonpos
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i))
    (hH : H ≤ 0) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by sorry
