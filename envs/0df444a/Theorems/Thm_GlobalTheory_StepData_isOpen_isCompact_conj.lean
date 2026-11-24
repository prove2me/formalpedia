-- Prove2me | Theorems.Thm_GlobalTheory_StepData_isOpen_isCompact_conj
-- name    : GlobalTheory.StepData.isOpen_isCompact_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:04.117338+00:00
-- url     : https://prove2.me/theorems/93599c58-e066-43d1-920c-59c44f6da0b1
-- title:
--   Step Data: is Open is Compact conj
-- statement:
--   The Step Data construction uses the is Open is Compact conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L596-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L596-L601

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
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.isOpen_isCompact_conj (g : GL Y k) {J : Subgroup (GL Y k)} (ho : IsOpen (J : Set (GL Y k)))
    (hc : IsCompact (J : Set (GL Y k))) :
    IsOpen (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) ∧
      IsCompact (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) := by sorry
