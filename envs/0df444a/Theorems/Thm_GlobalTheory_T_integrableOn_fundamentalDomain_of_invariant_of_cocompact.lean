-- Prove2me | Theorems.Thm_GlobalTheory_T_integrableOn_fundamentalDomain_of_invariant_of_cocompact
-- name    : GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:28.740505+00:00
-- url     : https://prove2.me/theorems/39857004-19f2-4b42-8e7f-d015923310ed
-- title:
--   T: integrable On fundamental Domain of invariant of cocompact
-- statement:
--   The T construction uses the integrable On fundamental Domain of invariant of cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IntegrableOnFundamentalDomainOfCocompactStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IntegrableOnFundamentalDomainOfCocompactStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by sorry
