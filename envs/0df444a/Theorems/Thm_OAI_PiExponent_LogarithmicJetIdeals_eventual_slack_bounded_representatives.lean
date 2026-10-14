-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_slack_bounded_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.eventual_slack_bounded_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T17:39:55.993299+00:00
-- url     : https://prove2.me/theorems/19b6d01b-b054-435a-8c21-d3c8899f99d2
-- title:
--   Eventual representatives with strict scale slack
-- statement:
--   There are positive scales R and S with R strictly below S, fixed positive jet exponents and truncation orders satisfying the row-weight bounds, and a threshold N such that every polynomial has a representative of weight at most nR modulo the nth power of this fixed simultaneous jet ideal for every n ≥ N. The strict gap is the ingredient needed to absorb any fixed additional ideal power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.eventual_slack_bounded_representatives
    {nu : ℝ} (d : FixedData nu) :
    ∃ R S : ℝ, 0 < R ∧ R < S ∧
      ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ,
        (∀ i, 0 < e i) ∧
        (∀ i, S ≤ (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        (∀ i : Fin d.m,
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
              (T i : ℝ) * (d.v0 : ℝ)) ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
            ∃ Q : WeightedPolynomial d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R),
              P - Q.val ∈ (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
                T e) ^ n := by sorry
