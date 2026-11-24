-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_bor_mem_parab
-- name    : GlobalTheory.PrinTwo.bor_mem_parab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:48.056295+00:00
-- url     : https://prove2.me/theorems/2441c8a7-ba05-485a-a964-8f6b5df8a3ca
-- title:
--   Prin Two: bor mem parab
-- statement:
--   The Prin Two construction uses the bor mem parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L98-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.PrinTwo.bor_mem_parab (a d : kˣ) (x : k) :
    bor a d x ∈ parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := by sorry
