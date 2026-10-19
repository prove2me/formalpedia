-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_produces_weighted_monic_relations
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_produces_weighted_monic_relations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T21:38:54.986838+00:00
-- url     : https://prove2.me/theorems/d5aa8877-9a52-4f98-b60e-9c0453d31b37
-- title:
--   Finite monic coordinate certificate under strict logarithmic jet capacity
-- statement:
--   Under the exact admissible-data, common-scale, strict capacity, and strict truncation hypotheses, construct finitely many polynomials in one positive power of the simultaneous jet ideal. Each polynomial has a pure coordinate power as its unique highest weighted term, and every pivot weight divided by the ideal-power index is bounded by one positive rate strictly below R. This is the open geometric construction required by the reduction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_produces_weighted_monic_relations
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ k : ℕ, 0 < k ∧
      ∃ a : ℝ, 0 < a ∧ a < R ∧
        ∃ b : Fin (d.m + 1) → ℕ, (∀ i, 0 < b i) ∧
          ∃ F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ,
            (∀ i, F i ∈
              (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d)) T e) ^ k) ∧
            (∀ i, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ) ≤ (k : ℝ) * a) ∧
            (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
              (∑ j, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                (u j : ℝ)) <
              InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ)) := by sorry
