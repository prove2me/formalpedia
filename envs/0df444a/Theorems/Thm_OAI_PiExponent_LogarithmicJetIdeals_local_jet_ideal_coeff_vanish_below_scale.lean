-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_coeff_vanish_below_scale
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_below_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T21:26:42.056967+00:00
-- url     : https://prove2.me/theorems/aa1c74f7-5517-47fc-bbdf-9dc2f0e6bc4d
-- title:
--   Local jet ideal coefficients vanish below their weighted scale
-- statement:
--   At any fixed center tuple, membership in the local jet ideal forces every formal-jet coefficient of weighted degree strictly below the generator scale to vanish. The lemma isolates the local weighted-filtration argument and applies independently of how the center tuple was selected.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_below_scale
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ localJetIdeal c T e)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c Q) = 0 := by sorry
