-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_scale_successor_coordinate
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale_successor_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T08:57:07.504585+00:00
-- url     : https://prove2.me/theorems/12bcc32a-d76d-41b5-85ac-573621b39eac
-- title:
--   Successor jet generator coefficient vanishes below scale
-- statement:
--   Every successor-coordinate generator has zero formal-jet coefficient at exponent vectors below the weighted scale; the truncation bound controls the logarithmic tail.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale_successor_coordinate
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    ∀ i : Fin m,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c
          (jetCoordinate c T i.succ ^ e i.succ)) = 0 := by sorry
