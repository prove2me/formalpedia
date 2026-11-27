-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_ae_fundamentalDomain_of_leftInvariant
-- name    : GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:10.572955+00:00
-- url     : https://prove2.me/theorems/d97f9fff-068d-4dcc-bfae-444ce30bd6d0
-- title:
--   Global Theory: eq zero of ae fundamental Domain of left Invariant
-- statement:
--   The Global Theory construction uses the eq zero of ae fundamental Domain of left Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfAeFundamentalDomainOfLeftInvariant.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfAeFundamentalDomainOfLeftInvariant.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfAeFundamentalDomainOfLeftInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory

theorem GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by sorry
