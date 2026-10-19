-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_substitution_generators_have_weighted_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.substitution_generators_have_weighted_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:29:24.38313+00:00
-- url     : https://prove2.me/theorems/71ad4aa9-b274-4835-a512-ae28511c32d6
-- title:
--   The shear generators preserve their assigned weight bound
-- statement:
--   For the family fixing `X 0` and replacing each later variable by `X i.succ + L i`, every generator has zero coefficients below its assigned coordinate weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.substitution_generators_have_weighted_support
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (L : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (L i) = 0) :
    ∀ (i : Fin (m + 1)) (α : Fin (m + 1) →₀ ℕ),
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < Fin.cases v0 u i →
        MvPowerSeries.coeff α
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + L i) i) = 0 := by sorry
