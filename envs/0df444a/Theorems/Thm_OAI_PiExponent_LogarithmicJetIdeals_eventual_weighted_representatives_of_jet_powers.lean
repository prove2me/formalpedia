-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_weighted_representatives_of_jet_powers
-- name    : OAI.PiExponent.LogarithmicJetIdeals.eventual_weighted_representatives_of_jet_powers
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T00:14:16.923853+00:00
-- url     : https://prove2.me/theorems/df7d9703-ae31-42d7-9edc-553db06d29e2
-- title:
--   Strict asymptotic weighted regularity of simultaneous logarithmic jet ideals
-- statement:
--   For full admissible separated-weight data and strict capacity slack, all sufficiently high simultaneous jet-ideal powers admit polynomial representatives at a positive weighted degree rate A strictly below R. This is the substantial geometric regularity child, which must be proved independently of dimension counting.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.eventual_weighted_representatives_of_jet_powers
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
    ∃ A : ℝ, 0 < A ∧ A < R ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          ∃ Q : WeightedPolynomial d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * A),
            P - Q.val ∈
              (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d)) T e) ^ n := by sorry
