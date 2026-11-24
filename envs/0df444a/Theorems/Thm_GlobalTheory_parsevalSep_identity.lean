-- Prove2me | Theorems.Thm_GlobalTheory_parsevalSep_identity
-- name    : GlobalTheory.parsevalSep_identity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:26.337338+00:00
-- url     : https://prove2.me/theorems/00ef5dca-422e-489e-bdc2-c6b5ba99ced0
-- title:
--   Global Theory: parseval Sep identity
-- statement:
--   The Global Theory construction uses the parseval Sep identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupport.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupport.lean#L35-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.parsevalSep_identity (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by sorry
