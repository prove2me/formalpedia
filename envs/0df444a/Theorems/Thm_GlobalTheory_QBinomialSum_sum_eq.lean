-- Prove2me | Theorems.Thm_GlobalTheory_QBinomialSum_sum_eq
-- name    : GlobalTheory.QBinomialSum.sum_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:01.457512+00:00
-- url     : https://prove2.me/theorems/1c960e08-8e57-488c-bcdb-53aea50e8586
-- title:
--   QBinomial Sum: sum eq
-- statement:
--   The QBinomial Sum construction uses the sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L23-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L23-L61

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

theorem GlobalTheory.QBinomialSum.sum_eq (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (n : ℕ) :
    ∑ a ∈ Finset.range n,
      (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = n := by sorry
