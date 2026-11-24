-- Prove2me | Theorems.Thm_GlobalTheory_ClassIntegral_integral_fundamentalDomain_eq_sum
-- name    : GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:54.652633+00:00
-- url     : https://prove2.me/theorems/7ff94c30-f9a7-47c8-8adf-d4442267c16f
-- title:
--   Class Integral: integral fundamental Domain eq sum
-- statement:
--   The Class Integral construction uses the integral fundamental Domain eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L93-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L93-L121

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

theorem GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by sorry
