-- Prove2me | Theorems.Thm_GlobalTheory_parsevalSep_orth
-- name    : GlobalTheory.parsevalSep_orth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:18.748037+00:00
-- url     : https://prove2.me/theorems/8ad3f3bc-fdaf-45ca-a9cc-3b7a9a922379
-- title:
--   Global Theory: parseval Sep orth
-- statement:
--   The Global Theory construction uses the parseval Sep orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupport.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupport.lean#L8-L33

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

theorem GlobalTheory.parsevalSep_orth (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by sorry
