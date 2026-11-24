-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
-- name    : GlobalTheory.StepData.mem_Cgrp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:15.091545+00:00
-- url     : https://prove2.me/theorems/c3730f88-4c4e-487e-98c6-16587790f595
-- title:
--   Step Data: mem Cgrp
-- statement:
--   The Step Data construction uses the mem Cgrp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L678-L680
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L678-L680

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
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.StepData.mem_Cgrp {J : Subgroup (GL (n ⊕ Fin c) k)} {h x : GL (n ⊕ Fin c) k} :
    x ∈ Cgrp J h ↔ x ∈ R k n c 1 ∧ h⁻¹ * x * h ∈ J := by sorry
