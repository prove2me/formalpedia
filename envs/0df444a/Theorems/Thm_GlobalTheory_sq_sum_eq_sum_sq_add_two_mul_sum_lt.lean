-- Prove2me | Theorems.Thm_GlobalTheory_sq_sum_eq_sum_sq_add_two_mul_sum_lt
-- name    : GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:48.497502+00:00
-- url     : https://prove2.me/theorems/0a0c5095-6c62-413e-b7a8-8530b382abc1
-- title:
--   Global Theory: sq sum eq sum sq add two mul sum lt
-- statement:
--   The Global Theory construction uses the sq sum eq sum sq add two mul sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqSumEqSumSqAddTwoMulSumLt.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqSumEqSumSqAddTwoMulSumLt.lean#L9-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqSumEqSumSqAddTwoMulSumLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
open Matrix Finset Real

theorem GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by sorry
