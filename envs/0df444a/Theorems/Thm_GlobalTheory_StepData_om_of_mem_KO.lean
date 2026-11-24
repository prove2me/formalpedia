-- Prove2me | Theorems.Thm_GlobalTheory_StepData_om_of_mem_KO
-- name    : GlobalTheory.StepData.om_of_mem_KO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:14.507637+00:00
-- url     : https://prove2.me/theorems/4d3b3cd9-b307-4661-890f-7a65b8bd8a0c
-- title:
--   Step Data: om of mem KO
-- statement:
--   The Step Data construction uses the om of mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1023-L1028
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1023-L1028

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
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.om_of_mem_KO (μ : kˣ →* ℂˣ) {g : GL a k} (hg : g ∈ KO k a) {h : GL b k}
    (hh : h ∈ KO k b) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) :
    om μ g h Φ x = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
      Φ ((h⁻¹).val * x * g.val) := by sorry
