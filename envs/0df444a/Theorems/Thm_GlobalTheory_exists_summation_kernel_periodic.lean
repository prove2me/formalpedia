-- Prove2me | Theorems.Thm_GlobalTheory_exists_summation_kernel_periodic
-- name    : GlobalTheory.exists_summation_kernel_periodic
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:52.387186+00:00
-- url     : https://prove2.me/theorems/da03f7e4-9128-432f-aea1-a77323a4b5ff
-- title:
--   Global Theory: exists summation kernel periodic
-- statement:
--   The Global Theory construction uses the exists summation kernel periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SetIntegralPosOfPeriodicNonneg.lean#L117-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SetIntegralPosOfPeriodicNonneg.lean#L117-L314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDescendPeriodicTrig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierCoeffMulCharConvAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SetIntegralPosOfPeriodicNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped Pointwise

theorem GlobalTheory.exists_summation_kernel_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ l : List (G → ℂ), (∀ Φ ∈ l, Continuous Φ ∧ ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ Φ ∈ l, ∀ x, ‖Φ x - ∑ a ∈ s, c a * ((∫ y in 𝓕, Φ y * starRingEnd ℂ (χ a y) ∂μ) * χ a x)‖ ≤ ε := by sorry
