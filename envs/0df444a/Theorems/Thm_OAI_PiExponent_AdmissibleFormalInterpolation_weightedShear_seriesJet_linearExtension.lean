-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet_linearExtension
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_linearExtension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:28:05.063169+00:00
-- url     : https://prove2.me/theorems/62dec3bd-a02e-41cf-87ea-c4bdb6f3fd8e
-- title:
--   Extend the monomial identity to polynomials
-- statement:
--   If the shear identity holds for every unit-coefficient monomial, complex linearity extends it to every polynomial through its finite monomial expansion.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_linearExtension
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hmono : ∀ e : Fin (m + 1) →₀ ℕ,
      (weightedShear (m := m) v0 u H D).toFun
          (weightedSeriesJet (m := m) v0 u H c F
            (MvPolynomial.monomial e 1)) =
        weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
          (MvPolynomial.monomial e 1)) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F P) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i) P := by sorry
