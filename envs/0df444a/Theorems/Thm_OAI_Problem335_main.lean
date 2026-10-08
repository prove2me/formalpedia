-- Prove2me | Theorems.Thm_OAI_Problem335_main
-- name    : OAI.Problem335.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.85698+00:00
-- url     : https://prove2.me/theorems/eeacd336-c7df-4b3a-bcf8-afaf5dd47246
-- statement:
--   The theorem states a three-part result about depth-five arithmetic circuits computing iterated matrix multiplication. A Depth5Circuit over a field K in n variables has leaves that are either scalars from K or variables X(t,i,j) indexed by triples in Fin n × Fin n × Fin n. Bottom gates are K-linear combinations of leaves, lower gates are products of bottom gates, middle gates are K-linear combinations of lower gates, upper gates are products of middle gates, and the output is a K-linear combination of upper gates. Each linear gate must be homogeneous, meaning all its inputs have the same formal degree (leaves have degree 0 or 1, products add degrees, and an empty sum has degree 0). The circuit's value is the resulting multivariate polynomial, and circuitSize is the number of leaves plus bottom, lower, middle and upper gates, plus one. The target polynomial imm(K,n) is the (0,0) entry of the product of the n generic n×n matrices whose t-th matrix has entries X(t,i,j), and is 0 when n=0. Part one: there is a threshold such that for every size n at or above it, every depth-five circuit over the complex numbers with n-indexed variables computing imm(ℂ,n) has circuitSize at least n^(√n/400). Part two: the same lower bound holds with a single threshold working uniformly for every field of characteristic zero in universe u. Part three: for every field K whatsoever and every n≥2, some depth-five circuit computes imm(K,n) with circuitSize at most upperGateBound(n), where, with t=⌈√n⌉ and r=⌈n/t⌉, upperGateBound(n) = 2n³ + r n² + r n^(t+1) + n^(r−1) + 1, and this quantity is itself at most n^(√n+4). The theorem is admitted in the source without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DepthFive.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DepthFive.lean; bytes 4030..4939
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DepthFive

namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace Problem335

theorem main :
    (∃ threshold : ℕ, ∀ size : ℕ, threshold ≤ size →
      ∀ circuit : Depth5Circuit ℂ size, circuitValue circuit = imm ℂ size →
        (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∃ threshold : ℕ, ∀ (FieldType : Type u) [Field FieldType] [CharZero FieldType],
      ∀ size : ℕ, threshold ≤ size → ∀ circuit : Depth5Circuit FieldType size,
        circuitValue circuit = imm FieldType size →
          (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∀ (FieldType : Type u) [Field FieldType] (size : ℕ), 2 ≤ size →
      ∃ circuit : Depth5Circuit FieldType size, circuitValue circuit = imm FieldType size ∧
        circuitSize circuit ≤ upperGateBound size ∧
        (upperGateBound size : ℝ) ≤ (size : ℝ) ^ (Real.sqrt (size : ℝ) + 4)) := by
  sorry

end Problem335
end
end OAI
