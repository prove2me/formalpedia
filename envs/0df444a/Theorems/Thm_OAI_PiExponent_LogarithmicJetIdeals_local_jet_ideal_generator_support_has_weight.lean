-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_support_has_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_support_has_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T11:45:12.058794+00:00
-- url     : https://prove2.me/theorems/172174f7-fea1-432b-9b27-556aedd26d65
-- title:
--   Supported successor jet monomials meet the row weight
-- statement:
--   Under the truncation-weight hypothesis, either possible support shape for a successor jet generator has weighted degree at least that coordinate’s row weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_support_has_weight
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ k, 0 < w k)
    (hT : ∀ k : Fin m,
      InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (hsupport :
      (∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0) ∨
        (T i ≤ b 0 ∧ ∀ j : Fin m, b j.succ = 0)) :
    InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) := by sorry
