-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_parahoric
-- name    : GlobalTheory.StepData.mem_parahoric
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:50:05.099801+00:00
-- url     : https://prove2.me/theorems/b14a9382-4a6e-4a46-a4bc-0019a7fe0ddc
-- title:
--   Step Data: mem parahoric
-- statement:
--   The Step Data construction uses the mem parahoric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L386-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L386-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

theorem GlobalTheory.StepData.mem_parahoric {δ : kˣ →* ℂˣ} {hδ : IsTame δ} {h : GL (r ⊕ s) k} :
    h ∈ (parahoric r s δ hδ).J ↔ h ∈ KO k (r ⊕ s) ∧ MaxM h.val.toBlocks₂₁ := by sorry
