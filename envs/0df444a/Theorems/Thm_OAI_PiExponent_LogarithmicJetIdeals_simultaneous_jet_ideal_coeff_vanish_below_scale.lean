-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_jet_ideal_coeff_vanish_below_scale
-- name    : OAI.PiExponent.LogarithmicJetIdeals.simultaneous_jet_ideal_coeff_vanish_below_scale
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T18:11:03.978903+00:00
-- url     : https://prove2.me/theorems/43d94379-4500-4451-8a08-a4cb18078dc5
-- title:
--   Simultaneous jet ideal coefficients vanish below their weighted scale
-- statement:
--   For any polynomial in the simultaneous jet ideal, every formal-jet coefficient at every center vanishes when its exponent vector has weighted degree strictly below R. The strict inequality preserves the truncation boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.simultaneous_jet_ideal_coeff_vanish_below_scale
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ simultaneousJetIdeal K r T e)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet
        (fun i => (j.val : ℂ) * r i) Q) = 0 := by sorry
