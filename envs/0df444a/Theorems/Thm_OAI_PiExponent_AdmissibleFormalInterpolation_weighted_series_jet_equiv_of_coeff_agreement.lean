-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:31:10.190024+00:00
-- url     : https://prove2.me/theorems/acd33fd6-14b9-4df9-a442-7ba1600074e5
-- title:
--   Series agreement induces an equivalence on weighted jet coefficients
-- statement:
--   If F_i and G_i agree in degrees strictly below N_i, with positive coordinate weights satisfying u_i ≤ N_i v0, their weighted jet coefficient maps differ by a linear equivalence independent of the center and polynomial. The equivalence comes from y_i ↦ y_i + F_i(x) − G_i(x). Both directions preserve weights at least H. Equality in the weight bound is allowed; nonpositive H gives an empty coefficient space, and m=0 gives the identity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i)) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by sorry
