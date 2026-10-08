-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_representative_scale_exists
-- name    : OAI.PiExponent.FormalInterpolation.weighted_representative_scale_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:29:18.716528+00:00
-- url     : https://prove2.me/theorems/a4ac5f9f-d4eb-4911-b163-47b9569c9156
-- title:
--   Existence of an admissible weighted representative scale
-- statement:
--   For every parameter $\\nu>2$ and admissible determinant family $d$, there are a positive rational scale $R$, natural-number cutoffs $T_i$, and positive integer exponents $e_i$ satisfying $$v_{i+1}\\le T_i v_0,\\qquad R=e_i v_i,$$ where $v_i$ is the row-weight sequence determined by $d$. This supplies the fixed scale data used in the eventual representative theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightedGeometryScale.lean (Scale and chooseScale); Ampleness/AdmissibleBlowupGeometry.lean (scale).

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.weighted_representative_scale_exists
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ (R : ℚ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ),
      0 < R ∧ (∀ i, 0 < e i) ∧
      (∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
        (T i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) 0) ∧
      (∀ i, (R : ℝ) = (e i : ℝ) *
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i) := by sorry
