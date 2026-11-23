-- Prove2me | Theorems.Thm_GlobalTheory_QBinomialSum_den_ne
-- name    : GlobalTheory.QBinomialSum.den_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:56.453897+00:00
-- url     : https://prove2.me/theorems/a3c43259-2ae6-4d93-9cf2-16184e796ded
-- title:
--   QBinomial Sum: den ne
-- statement:
--   The QBinomial Sum construction uses the den ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean#L15-L21

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

theorem GlobalTheory.QBinomialSum.den_ne (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (a : ℕ) :
    ∏ i ∈ Finset.range a, (x ^ a - x ^ i) ≠ 0 := by sorry
