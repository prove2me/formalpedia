-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Growth_lintegral_le_mul_of_encard_le
-- name    : GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:58.953966+00:00
-- url     : https://prove2.me/theorems/3db81bac-1e9d-44a3-9eef-f9c5bfe8dd33
-- title:
--   Growth: lintegral le mul of encard le
-- statement:
--   The Growth construction uses the lintegral le mul of encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainIntegralCountBound.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainIntegralCountBound.lean#L7-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Growth

theorem GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (M : Set G) (hM : MeasurableSet M) (f : G → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (n : ℕ)
    (hn : ∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) :
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by sorry
