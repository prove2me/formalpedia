-- Prove2me | Theorems.Thm_GlobalTheory_StepData_om_support_period
-- name    : GlobalTheory.StepData.om_support_period
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:42.282093+00:00
-- url     : https://prove2.me/theorems/26611228-51dd-4507-b3e1-72275c4b49c4
-- title:
--   Step Data: om support period
-- statement:
--   The Step Data construction uses the om support period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearWeilActionSupportAndPeriodIntegral.lean#L8-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearWeilActionSupportAndPeriodIntegral.lean#L8-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearWeilActionSupportAndPeriodIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.StepData

theorem GlobalTheory.StepData.om_support_period : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by sorry
