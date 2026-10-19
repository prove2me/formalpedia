-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement_pos
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_pos
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:44:24.885585+00:00
-- url     : https://prove2.me/theorems/6c8a2323-ed84-4886-be60-e9785665b63f
-- title:
--   Weighted series jet substitution for a positive cutoff
-- statement:
--   For a positive strict cutoff, the change of variables translating each jet coordinate by the series difference preserves the weighted coefficient filtration, in both directions, and induces the required linear equivalence on coefficient functions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_pos
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i))
    (hH : 0 < H) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by sorry
