-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_scale_integer_row_weights
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_scale_integer_row_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T22:14:07.637678+00:00
-- url     : https://prove2.me/theorems/55787f63-63b8-4e52-8c44-68851e6d6c49
-- title:
--   Compatible strict scales with integer row multiplicities
-- statement:
--   Choose a positive scale S that is a positive integer multiple of each row weight, together with a strictly smaller positive scale R close enough to S to satisfy the volume-capacity inequality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_scale_integer_row_weights
    {nu : ℝ} (d : FixedData nu) :
    ∃ R S : ℝ, 0 < R ∧ R < S ∧
      ∃ e : Fin (d.m + 1) → ℕ, (∀ i, 0 < e i) ∧
        (∀ i, S = (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ) := by sorry
