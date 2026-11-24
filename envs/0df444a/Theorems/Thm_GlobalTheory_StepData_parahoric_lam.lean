-- Prove2me | Theorems.Thm_GlobalTheory_StepData_parahoric_lam
-- name    : GlobalTheory.StepData.parahoric_lam
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:08.089312+00:00
-- url     : https://prove2.me/theorems/58d0ec61-c435-4145-ba57-12e8f9bcf993
-- title:
--   Step Data: parahoric lam
-- statement:
--   The Step Data construction uses the parahoric lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L391-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L391-L395

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

theorem GlobalTheory.StepData.parahoric_lam {δ : kˣ →* ℂˣ} {hδ : IsTame δ} (h : (parahoric r s δ hδ).J) (D : GL s k)
    (hD : D.val = (h : GL (r ⊕ s) k).val.toBlocks₂₂) :
    (parahoric r s δ hδ).lam h = δ (Matrix.GeneralLinearGroup.det D) := by sorry
