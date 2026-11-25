-- Prove2me | Theorems.Thm_GlobalTheory_PartialIntegral_locallyConstant_partial
-- name    : GlobalTheory.PartialIntegral.locallyConstant_partial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:56.786271+00:00
-- url     : https://prove2.me/theorems/99755ba5-e9bc-5ef1-9467-cd94c7e359b4
-- title:
--   Partial Integral: locally Constant partial
-- statement:
--   The Partial Integral construction uses the locally Constant partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L128-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L128-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocallyConstantPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.PartialIntegral
variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem GlobalTheory.PartialIntegral.locallyConstant_partial {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g)
    {M₁ : Y → W} {M₂ : B → W} {Q₁ : W → Y} {Q₂ : W → B} (c₁ : Continuous M₁) (c₂ : Continuous M₂) (d₁ : Continuous Q₁)
    (d₂ : Continuous Q₂) (e₁ : ∀ y b, Q₁ (M₁ y + M₂ b) = y) (e₂ : ∀ y b, Q₂ (M₁ y + M₂ b) = b) :
    (∀ b, Integrable (fun y => g (M₁ y + M₂ b)) ν) ∧ IsLocallyConstant (fun b => ∫ y, g (M₁ y + M₂ b) ∂ν) ∧
      HasCompactSupport fun b => ∫ y, g (M₁ y + M₂ b) ∂ν := by sorry
