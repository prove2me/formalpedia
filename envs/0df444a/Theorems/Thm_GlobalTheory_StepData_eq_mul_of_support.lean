-- Prove2me | Theorems.Thm_GlobalTheory_StepData_eq_mul_of_support
-- name    : GlobalTheory.StepData.eq_mul_of_support
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:15.01056+00:00
-- url     : https://prove2.me/theorems/c7521c39-91a1-42a0-a918-80f35652460b
-- title:
--   Step Data: eq mul of support
-- statement:
--   The Step Data construction uses the eq mul of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1010-L1019
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1010-L1019

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

theorem GlobalTheory.StepData.eq_mul_of_support {G S : Type*} [Group G] (act : G → S → S) (hact : ∀ g x, act g⁻¹ (act g x) = x)
    {f : S → ℂ} {c : G → ℂˣ} (h : ∀ g x, f x ≠ 0 → f (act g x) = c g * f x) (g : G) (x : S) :
    f (act g x) = c g * f x := by sorry
