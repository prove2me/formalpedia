-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_sub_inv_mul_out_mem_iff
-- name    : GlobalTheory.HeisUnit.sub_inv_mul_out_mem_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:53.771775+00:00
-- url     : https://prove2.me/theorems/3eb1f030-7bf2-4657-bf3c-9b5a22859fd8
-- title:
--   Heis Unit: sub inv mul out mem iff
-- statement:
--   The Heis Unit construction uses the sub inv mul out mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L17-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L17-L42

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

theorem GlobalTheory.HeisUnit.sub_inv_mul_out_mem_iff {ϖ : kˣ} (hϖ : SplitFlip.IsUnif ϖ) (y : k) (t : SplitFlip.Res k 1) :
    y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
      ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by sorry
