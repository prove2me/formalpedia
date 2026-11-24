-- Prove2me | Theorems.Thm_GlobalTheory_FlatFamily_aestronglyMeasurable_flatIntegrand
-- name    : GlobalTheory.FlatFamily.aestronglyMeasurable_flatIntegrand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:34.332806+00:00
-- url     : https://prove2.me/theorems/44c646f8-6d22-417c-bbdd-2cec85daf7aa
-- title:
--   Flat Family: aestrongly Measurable flat Integrand
-- statement:
--   The Flat Family construction uses the aestrongly Measurable flat Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L31-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.FlatFamily
open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]

theorem GlobalTheory.FlatFamily.aestronglyMeasurable_flatIntegrand {μ : Measure X} {f : X → ℂ} {a : X → ℝ}
    (hm : Measurable a) (ha : ∀ x, 0 < a x) {s₀ s₁ : ℂ}
    (h : AEStronglyMeasurable (flatIntegrand f a s₀ s₁) μ) (s : ℂ) :
    AEStronglyMeasurable (flatIntegrand f a s₀ s) μ := by sorry
