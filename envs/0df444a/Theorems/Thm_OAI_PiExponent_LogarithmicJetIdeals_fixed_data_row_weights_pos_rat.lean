-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_fixed_data_row_weights_pos_rat
-- name    : OAI.PiExponent.LogarithmicJetIdeals.fixed_data_row_weights_pos_rat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T19:06:38.999474+00:00
-- url     : https://prove2.me/theorems/a11e5e30-cb5e-4be4-9f99-e805a33a6df9
-- title:
--   Fixed-data row weights are positive rationals
-- statement:
--   For every row index, the fixed-data row weight is positive and is the real cast of a rational number. The zeroth entry follows from `v0_pos` and rationality of `v0`; the other entries use the positive logarithm ceilings and rationality and positivity of `theta`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.fixed_data_row_weights_pos_rat
    {nu : ℝ} (d : FixedData nu) :
    ∀ i : Fin (d.m + 1),
      0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i ∧
        ∃ q : ℚ, InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i = (q : ℝ) := by sorry
