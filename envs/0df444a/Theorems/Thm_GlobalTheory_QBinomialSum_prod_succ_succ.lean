-- Prove2me | Theorems.Thm_GlobalTheory_QBinomialSum_prod_succ_succ
-- name    : GlobalTheory.QBinomialSum.prod_succ_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:53.274585+00:00
-- url     : https://prove2.me/theorems/dc9a03ac-1f81-44d0-9120-f59fc773b6e1
-- title:
--   QBinomial Sum: prod succ succ
-- statement:
--   The QBinomial Sum construction uses the prod succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L7-L13

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

theorem GlobalTheory.QBinomialSum.prod_succ_succ (x : ℂ) (n a : ℕ) :
    ∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)
      = (x ^ (n + 1) - 1) * x ^ a * ∏ i ∈ Finset.range a, (x ^ n - x ^ i) := by sorry
