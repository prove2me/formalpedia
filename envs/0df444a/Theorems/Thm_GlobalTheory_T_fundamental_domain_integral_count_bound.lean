-- Prove2me | Theorems.Thm_GlobalTheory_T_fundamental_domain_integral_count_bound
-- name    : GlobalTheory.T.fundamental_domain_integral_count_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:59.898943+00:00
-- url     : https://prove2.me/theorems/2f24b76a-5672-4704-be0a-7a80e66bc473
-- title:
--   T: fundamental domain integral count bound
-- statement:
--   The T construction uses the fundamental domain integral count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainIntegralCountBoundStatement.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainIntegralCountBoundStatement.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBoundStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fundamental_domain_integral_count_bound : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (M : Set G), MeasurableSet M → ∀ (f : G → ℝ≥0∞), Measurable f →
    (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → ∀ n : ℕ, (∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) →
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by sorry
