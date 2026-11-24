-- Prove2me | Theorems.Thm_GlobalTheory_QBinomialSum_sum_gaussian_mul_prod
-- name    : GlobalTheory.QBinomialSum.sum_gaussian_mul_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:03.753883+00:00
-- url     : https://prove2.me/theorems/a0e3c30d-2d2e-4a60-9267-31b951efc60c
-- title:
--   QBinomial Sum: sum gaussian mul prod
-- statement:
--   The QBinomial Sum construction uses the sum gaussian mul prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L63-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.QBinomialSum

theorem GlobalTheory.QBinomialSum.sum_gaussian_mul_prod : ∀ (q n : ℕ) (N : ℕ → ℕ), 2 ≤ q → (∀ a, a ≤ n → N a * ∏ i ∈ Finset.range a, (q ^ a - q ^ i) = ∏ i ∈ Finset.range a, (q ^ n - q ^ i)) → ∑ a ∈ Finset.Icc 1 n, (N a : ℂ) * ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i) = n := by sorry
