-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldMain_omega_lt_source_constant
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:55.308978+00:00
-- url     : https://prove2.me/theorems/38c6efcc-67b9-443f-b90f-8b10ec2aeaf2
-- statement:
--   The theorem states that for every field F (in any universe), the matrix-multiplication exponent omega(F) is strictly less than the real number 2371054886006746/10^15, and that this number is in turn strictly less than 2371056/10^6, so omega(F) < 2.371054886006746 < 2.371056. Here omega(F) is defined as the infimum of the set of admissible exponents τ. An exponent τ is admissible if, for every ε>0, there is a constant C>0 such that for every n≥1 there is a correct straight-line arithmetic program multiplying n×n matrices over F, meaning that it outputs A·B for all input matrices A and B, using at most C·n^(τ+ε) gates. Programs are sequences of registers, each computed by a gate that is a constant of F, an input matrix entry, or the sum, difference or product of two earlier registers. The cost counts add, subtract and multiply gates as one each, while constants and inputs are free.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatrixFields.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatrixFields.lean; bytes 3027..3228
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MatrixFields

namespace OAI

open scoped BigOperators Topology Polynomial

namespace MatrixAllFields.MatrixMultiplication.AllFieldMain

universe u

theorem omega_lt_source_constant (F : Type u) [Field F] :
    Arithmetic.omega F < (2371054886006746 : ℝ) / 10 ^ 15 ∧
    (2371054886006746 : ℝ) / 10 ^ 15 < (2371056 : ℝ) / 10 ^ 6 := by
  sorry

end MatrixAllFields.MatrixMultiplication.AllFieldMain
end OAI
