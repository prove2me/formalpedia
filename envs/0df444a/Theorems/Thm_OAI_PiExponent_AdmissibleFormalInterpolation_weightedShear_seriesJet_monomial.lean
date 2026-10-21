-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet_monomial
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:27:21.836919+00:00
-- url     : https://prove2.me/theorems/10767b78-b39c-44fe-898c-3c395123f3e0
-- title:
--   Weighted shear identity on polynomial monomials
-- statement:
--   Under the positive-weight, strict-cutoff, vanishing, and weight-bound hypotheses, the finite coefficient shear intertwines series jets of each unit-coefficient polynomial monomial, including the constant monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_monomial
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (e : Fin (m + 1) →₀ ℕ) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F
          (MvPolynomial.monomial e 1)) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
        (MvPolynomial.monomial e 1) := by sorry
