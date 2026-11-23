-- Prove2me | Theorems.Thm_GlobalTheory_exists_strict_measurable_fundamental_set_of_discrete
-- name    : GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:38.317417+00:00
-- url     : https://prove2.me/theorems/ca69e7a9-6872-4ee6-890b-9d1fb9a6afd6
-- title:
--   Global Theory: exists strict measurable fundamental set of discrete
-- statement:
--   The Global Theory construction uses the exists strict measurable fundamental set of discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsStrictMeasurableFundamentalSetOfDiscrete.lean#L11-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsStrictMeasurableFundamentalSetOfDiscrete.lean#L11-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStrictMeasurableFundamentalSetOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

theorem GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by sorry
