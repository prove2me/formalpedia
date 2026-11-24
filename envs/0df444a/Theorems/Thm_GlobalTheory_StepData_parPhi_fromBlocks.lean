-- Prove2me | Theorems.Thm_GlobalTheory_StepData_parPhi_fromBlocks
-- name    : GlobalTheory.StepData.parPhi_fromBlocks
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:02.446386+00:00
-- url     : https://prove2.me/theorems/d5fa3efe-a2e9-43d9-87ac-3e8df92885d2
-- title:
--   Step Data: par Phi from Blocks
-- statement:
--   The Step Data construction uses the par Phi from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L410-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L410-L413

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
omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.parPhi_fromBlocks (δ : kˣ →* ℂˣ) {A : Matrix r r k} {B : Matrix r s' k} {C : Matrix s r k} {D : Matrix s s' k}
    {g : GL r k} (hg : g ∈ KO k r) (e : g.val = A) (h21 : MaxM C) (h12 : IntM B) (h22 : IntM D) :
    parPhi δ (fromBlocks A B C D) = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) := by sorry
