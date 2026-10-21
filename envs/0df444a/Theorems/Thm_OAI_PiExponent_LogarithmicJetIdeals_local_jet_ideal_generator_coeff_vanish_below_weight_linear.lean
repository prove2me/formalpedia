-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_weight_linear
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight_linear
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T10:49:11.464063+00:00
-- url     : https://prove2.me/theorems/91513520-e2d6-4090-abe4-9e0c33ec5758
-- title:
--   Linear successor jet generator has no coefficients below its weight
-- statement:
--   Under the parent’s positivity and truncation hypotheses, coefficients of the formal image of a successor jet generator vanish whenever the exponent vector’s weighted degree is strictly below that coordinate’s row weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight_linear
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (b : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0) :
    ∀ i : Fin m,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) <
        InterpolationMatrix.rowWeights v0 theta w i.succ →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c
          (jetCoordinate c T i.succ)) = 0 := by sorry
