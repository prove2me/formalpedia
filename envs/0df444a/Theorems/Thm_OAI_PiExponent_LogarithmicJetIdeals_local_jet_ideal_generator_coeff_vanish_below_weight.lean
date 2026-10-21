-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T10:14:50.961934+00:00
-- url     : https://prove2.me/theorems/8644a4e7-7a49-4989-9482-9f05ca4a5dc4
-- title:
--   Successor jet generator coefficient vanishes below its weight bound
-- statement:
--   For positive coordinate weights and truncation bounds, every coefficient of the nth power of a successor jet generator vanishes when the exponent vector has weighted degree strictly below n times that successor coordinate’s row weight. The cutoff is strict, matching the fact that truncation at T retains degrees strictly below T.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (n : ℕ) (b : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0) :
    ∀ i : Fin m,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) <
        (n : ℝ) * InterpolationMatrix.rowWeights v0 theta w i.succ →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c
          (jetCoordinate c T i.succ ^ n)) = 0 := by sorry
