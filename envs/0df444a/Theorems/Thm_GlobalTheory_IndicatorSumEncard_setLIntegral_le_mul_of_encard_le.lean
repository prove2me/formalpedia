-- Prove2me | Theorems.Thm_GlobalTheory_IndicatorSumEncard_setLIntegral_le_mul_of_encard_le
-- name    : GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:21.132874+00:00
-- url     : https://prove2.me/theorems/1029937f-515b-4d27-b427-f9ccd2a70020
-- title:
--   Indicator Sum Encard: set LIntegral le mul of encard le
-- statement:
--   The Indicator Sum Encard construction uses the set LIntegral le mul of encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SetLIntegralLeMulOfEncardLe.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SetLIntegralLeMulOfEncardLe.lean#L12-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SetLIntegralLeMulOfEncardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IndicatorSumEncard

theorem GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [Measure.IsMulLeftInvariant μ] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G}
    (hD : IsFundamentalDomain (↥Γ) D μ) {f : G → ENNReal} (hf : AEMeasurable f μ)
    (hinv : ∀ᵐ (y : G) ∂μ, ∀ (γ : ↥Γ), f ((↑γ : G) * y) = f y) {S : Set G}
    (hS : MeasurableSet S) (N : ENNReal) (hN : N ≠ ⊤)
    (hcount : ∀ (z : G), (↑(Set.encard {γ : ↥Γ | (↑γ : G) * z ∈ S}) : ENNReal) ≤ N) :
    ∫⁻ (y : G) in S, f y ∂μ ≤ N * ∫⁻ (y : G) in D, f y ∂μ := by sorry
