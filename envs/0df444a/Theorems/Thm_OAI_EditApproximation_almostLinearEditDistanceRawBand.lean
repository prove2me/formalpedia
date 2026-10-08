-- Prove2me | Theorems.Thm_OAI_EditApproximation_almostLinearEditDistanceRawBand
-- name    : OAI.EditApproximation.almostLinearEditDistanceRawBand
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:36.643763+00:00
-- url     : https://prove2.me/theorems/224e24e0-232a-46bb-b462-937b57fd9eae
-- statement:
--   The theorem states that, for every binary-fraction accuracy parameter epsilon (a rational given by a signed binary numerator and a positive binary denominator) whose value lies strictly between 0 and 1, a randomized edit-distance approximation procedure for lists of integers, run with size bound N, satisfies four properties. Integers are encoded as natural-number symbols, and the procedure's randomness is the law computedFullLaw of its computed execution, with its output given by integerBinaryAnswerRawBand. First, for all integer lists source and target with total length at most N, with probability at least 2/3 the output is at least the true edit distance and at most (1 + epsilon) times the true edit distance. Second, whenever source equals target, the output is 0 for every outcome. Third, for every exponent C in the naturals and every eta > 0, for all sufficiently large N, every pair with total length at most N and all entries z satisfying |z| <= (N+2)^C has expected work, the integral of integerBinaryWorkRawBand under that law, at most (N+2)^(1+eta). Fourth, for every C, for all sufficiently large N, under the same length and entry-size conditions, the space footprint integerBinarySpaceFootprintRawBand is at most (N+2)^(C+65564) for every outcome. The theorem is admitted without a proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean; bytes 1424702..1426510
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EditApproximation

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

attribute [local instance] queryRoundsNeZero

theorem almostLinearEditDistanceRawBand (epsilon : OAI.EditApproximation.BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (OAI.EditApproximation.computedFullLaw (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ OAI.EditApproximation.integerBinaryAnswerRawBand source target N epsilon outcome ∧
          (OAI.EditApproximation.integerBinaryAnswerRawBand source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * OAI.EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      OAI.EditApproximation.integerBinaryAnswerRawBand source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, OAI.EditApproximation.integerBinaryWorkRawBand source target N epsilon outcome
          ∂OAI.EditApproximation.computedFullLaw (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, OAI.EditApproximation.integerBinarySpaceFootprintRawBand source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  sorry

end OAI.EditApproximation
end
