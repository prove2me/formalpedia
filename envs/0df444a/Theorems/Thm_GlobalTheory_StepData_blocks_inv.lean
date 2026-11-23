-- Prove2me | Theorems.Thm_GlobalTheory_StepData_blocks_inv
-- name    : GlobalTheory.StepData.blocks_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:33.367919+00:00
-- url     : https://prove2.me/theorems/43a9d243-8bbf-4e23-8776-f01974517bf8
-- title:
--   Step Data: blocks inv
-- statement:
--   The Step Data construction uses the blocks inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L179-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L179-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
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
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.blocks_inv {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t)) (hC : MaxM h.val.toBlocks₂₁) :
    MaxM (h.val.toBlocks₁₁ * (h⁻¹).val.toBlocks₁₁ - 1) ∧ MaxM (h.val.toBlocks₂₂ * (h⁻¹).val.toBlocks₂₂ - 1) ∧
      MaxM (h⁻¹).val.toBlocks₂₁ := by sorry
