-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_mem_stepJ
-- name    : GlobalTheory.StepData.TypeDatum.mem_stepJ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:50:02.283823+00:00
-- url     : https://prove2.me/theorems/de6b4492-6349-48f3-a1d4-6a4bc88b6dbd
-- title:
--   Type Datum: mem step J
-- statement:
--   The Type Datum construction uses the mem step J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L218-L219

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
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)

theorem GlobalTheory.StepData.TypeDatum.mem_stepJ {h : GL (a ⊕ t) k} : h ∈ P.stepJ t ↔ h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧
    IntM h.val.toBlocks₁₂ ∧ MaxM h.val.toBlocks₂₁ ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂ := by sorry
