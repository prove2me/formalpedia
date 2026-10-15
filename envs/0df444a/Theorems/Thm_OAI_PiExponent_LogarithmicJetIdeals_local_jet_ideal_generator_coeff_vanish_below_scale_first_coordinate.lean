-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_scale_first_coordinate
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale_first_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T08:56:41.841839+00:00
-- url     : https://prove2.me/theorems/60c84156-fa03-4041-ba97-a6d91612e90f
-- title:
--   First-coordinate jet generator coefficient vanishes below scale
-- statement:
--   The first-coordinate generator has zero formal-jet coefficient at every exponent vector whose weighted degree is below the scale bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale_first_coordinate
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T (0 : Fin (m + 1)) ^ e (0 : Fin (m + 1))) ) = 0 := by sorry
