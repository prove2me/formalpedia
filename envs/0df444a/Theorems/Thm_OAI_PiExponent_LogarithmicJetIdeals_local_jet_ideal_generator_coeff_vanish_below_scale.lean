-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_scale
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T23:59:41.408034+00:00
-- url     : https://prove2.me/theorems/01067c1d-23c9-4aa7-8a71-19e32029ac04
-- title:
--   Jet ideal generators have no coefficients below their weighted scale
-- statement:
--   For every generator coordinate and exponent of weighted degree strictly below R, its powered jet-coordinate formal-jet coefficient vanishes. The successor-coordinate case accounts for the logarithmic tail after truncation at T i.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    ∀ i : Fin (m + 1),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i ^ e i)) = 0 := by sorry
