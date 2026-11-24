-- Prove2me | Theorems.Thm_GlobalTheory_ClassIntegral_measure_dcoset
-- name    : GlobalTheory.ClassIntegral.measure_dcoset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:26:43.781536+00:00
-- url     : https://prove2.me/theorems/4c4f6228-162e-4609-8555-f80253bbc73a
-- title:
--   Class Integral: measure dcoset
-- statement:
--   The Class Integral construction uses the measure dcoset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L49-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L49-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem GlobalTheory.ClassIntegral.measure_dcoset (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by sorry
