-- Prove2me | Theorems.Thm_OAI_Kadison_uniform_commutator
-- name    : OAI.Kadison.uniform_commutator
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:50.477242+00:00
-- url     : https://prove2.me/theorems/b364ae25-c675-41eb-8cc0-485af05626a8
-- statement:
--   For a complex Hilbert space K (a complete complex inner product space) and a von Neumann algebra P of bounded operators on K, the commutator seminorm of an operator Y is defined as the supremum of ‖Ya − aY‖ over all a in P with ‖a‖ ≤ 1. For a positive integer h, a matrix X of bounded operators on K is viewed as a single bounded operator on the direct sum of h copies of K (with the ℓ² norm) by ordinary matrix multiplication, and Y is amplified to the diagonal operator acting as Y on each coordinate. The theorem states that there is a real constant C ≥ 0, independent of K, P, Y, h and X, such that for every complex Hilbert space K in the given universe, every von Neumann algebra P on K, every bounded operator Y on K, every h ≥ 1, and every h×h matrix X over the bounded operators on K all of whose entries lie in P, the operator norm of the commutator of the diagonal amplification of Y with the operator of X is at most C times the commutator seminorm of Y with respect to P times the operator norm of X. The statement is recorded as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformCommutator.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformCommutator.lean; bytes 1009..1510
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_UniformCommutator

namespace OAI

noncomputable section

universe u v

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

theorem uniform_commutator :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
      (h : ℕ), 1 ≤ h → ∀ (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)),
      (∀ i j, X i j ∈ P) →
      ‖diagonalAmplification h Y * matrixOperator h X -
        matrixOperator h X * diagonalAmplification h Y‖ ≤
        C * commutatorSeminorm P Y * ‖matrixOperator h X‖ := by
  sorry

end Kadison
end
end OAI
