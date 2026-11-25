-- Prove2me | Theorems.Thm_GlobalTheory_PartialIntegral_schwartz_partial
-- name    : GlobalTheory.PartialIntegral.schwartz_partial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:15:22.398277+00:00
-- url     : https://prove2.me/theorems/ee4ee08f-2702-40cc-8128-4896b5ea30ae
-- title:
--   Partial Integral: schwartz partial
-- statement:
--   The Partial Integral construction uses the schwartz partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L91-L98

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
variable {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem GlobalTheory.PartialIntegral.schwartz_partial [FiniteDimensional ℝ A] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ))
    (L₁ : X →ₗ[ℝ] V) (L₂ : A →ₗ[ℝ] V) (hL : ∀ x a, L₁ x + L₂ a = 0 → x = 0 ∧ a = 0) :
    (∀ a, Integrable (fun x => f (L₁ x + L₂ a)) μ) ∧ ∃ h : 𝓢(A, ℂ), ∀ a, h a = ∫ x, f (L₁ x + L₂ a) ∂μ := by sorry
