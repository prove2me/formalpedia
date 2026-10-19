-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_eventual_polynomialJet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_eventual_polynomialJet_interpolation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T21:58:28.759884+00:00
-- url     : https://prove2.me/theorems/fee76b09-f845-4744-b895-594ab0e182b3
-- title:
--   Eventual weighted interpolation on logarithmic jet staircases
-- statement:
--   Under the exact admissible-data, common-scale, strict capacity, and strict truncation hypotheses, every sufficiently large logarithmic jet staircase admits arbitrary coefficient interpolation by a polynomial of column-weighted degree at most the power index times the radius.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_eventual_polynomialJet_interpolation
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
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ f : Fin d.K → (Fin (d.m + 1) →₀ ℕ) → ℂ,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
          (∀ u ∈ Q.support,
            (∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
              (u i : ℝ)) ≤ (k : ℝ) * R) ∧
          (∀ j : Fin d.K, ∀ u : Fin (d.m + 1) →₀ ℕ,
            (∑ i, u i / e i) < k →
              MvPolynomial.coeff u
                (polynomialJet
                  (fun i => (j.val : ℂ) *
                    MatrixArithmetic.rationalCenters (finiteNumerators d)
                      (finiteDenominators d) i) T Q) = f j u) := by sorry
