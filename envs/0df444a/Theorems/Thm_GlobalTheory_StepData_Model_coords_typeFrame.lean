-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_coords_typeFrame
-- name    : GlobalTheory.StepData.Model.coords_typeFrame
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:11.197501+00:00
-- url     : https://prove2.me/theorems/77c270ec-af6a-4616-974c-566e9a20f04a
-- title:
--   Model: coords type Frame
-- statement:
--   The Model construction uses the coords type Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L114-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.Model.coords_typeFrame (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (i : ι) (j : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x i j = (wt ϖ (o i))⁻¹ * x (o i) (o' j) * wt ϖ (o' j) := by sorry
