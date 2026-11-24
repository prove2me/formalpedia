-- Prove2me | Theorems.Thm_GlobalTheory_StepData_parPhi_of_mem
-- name    : GlobalTheory.StepData.parPhi_of_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:20.505035+00:00
-- url     : https://prove2.me/theorems/c487199b-0d3a-4a70-b2f8-b70c975cdcf9
-- title:
--   Step Data: par Phi of mem
-- statement:
--   The Step Data construction uses the par Phi of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L404-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L404-L407

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

theorem GlobalTheory.StepData.parPhi_of_mem (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} {g : GL r k} (hg : g ∈ KO k r)
    (e : g.val = x.toBlocks₁₁) (h21 : MaxM x.toBlocks₂₁) (h12 : IntM x.toBlocks₁₂) (h22 : IntM x.toBlocks₂₂) :
    parPhi δ x = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) := by sorry
