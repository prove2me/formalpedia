-- Prove2me | Theorems.Thm_GlobalTheory_StepData_tame_det_blocks
-- name    : GlobalTheory.StepData.tame_det_blocks
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:39.08482+00:00
-- url     : https://prove2.me/theorems/76fdbcc2-e98f-4c24-9df7-e770e22256aa
-- title:
--   Step Data: tame det blocks
-- statement:
--   The Step Data construction uses the tame det blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L221-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L221-L238

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

theorem GlobalTheory.StepData.tame_det_blocks {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t))
    (hC : MaxM h.val.toBlocks₂₁) {g : GL a k} (hg : g.val = h.val.toBlocks₁₁) {D : GL t k}
    (hD : D.val = h.val.toBlocks₂₂) :
    μ (Matrix.GeneralLinearGroup.det h) =
      μ (Matrix.GeneralLinearGroup.det g) * μ (Matrix.GeneralLinearGroup.det D) := by sorry
