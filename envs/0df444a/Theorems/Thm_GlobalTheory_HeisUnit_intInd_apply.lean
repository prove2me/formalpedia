-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_intInd_apply
-- name    : GlobalTheory.HeisUnit.intInd_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:11.852548+00:00
-- url     : https://prove2.me/theorems/fd1b7f86-07ee-4555-aff4-21a62ed7bf46
-- title:
--   Heis Unit: int Ind apply
-- statement:
--   The Heis Unit construction uses the int Ind apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubInvMulOutMemIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Classical

theorem GlobalTheory.HeisUnit.intInd_apply {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by sorry
