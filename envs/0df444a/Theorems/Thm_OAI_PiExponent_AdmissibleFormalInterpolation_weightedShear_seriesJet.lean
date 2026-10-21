-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:01:37.925197+00:00
-- url     : https://prove2.me/theorems/d93c6301-5a93-4693-bb30-ec272f16513b
-- title:
--   Explicit weighted coefficient shear intertwines polynomial series jets
-- statement:
--   Under positive weights, positive strict cutoff, and the vanishing and weight bounds for D, the finite coefficient shear sends the polynomial series jet for any background family F to that for F + D. No vanishing assumption on F is required. Preservation of weight prevents discarded coefficients, including those of weight exactly H, from contributing below H. The assertion also includes m = 0 and cutoffs retaining only constants.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F P) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i) P := by sorry
