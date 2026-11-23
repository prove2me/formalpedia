-- Prove2me | Theorems.Thm_GlobalTheory_integrableOn_fundamentalDomain_of_cocompact
-- name    : GlobalTheory.integrableOn_fundamentalDomain_of_cocompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:27.080298+00:00
-- url     : https://prove2.me/theorems/4ac30006-b1dc-4870-bf65-db012243259e
-- title:
--   Global Theory: integrable On fundamental Domain of cocompact
-- statement:
--   The Global Theory construction uses the integrable On fundamental Domain of cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IntegrableOnFundamentalDomainOfCocompact.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IntegrableOnFundamentalDomainOfCocompact.lean#L9-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory
open Pointwise

theorem GlobalTheory.integrableOn_fundamentalDomain_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by sorry
