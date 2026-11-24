-- Prove2me | Theorems.Thm_GlobalTheory_MeasurableFundamentalDomain_exists_measurable_fundamental_domain
-- name    : GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:39.159336+00:00
-- url     : https://prove2.me/theorems/b5fcf263-a7bc-49e8-860f-0d443419bc2a
-- title:
--   Measurable Fundamental Domain: exists measurable fundamental domain
-- statement:
--   The Measurable Fundamental Domain construction uses the exists measurable fundamental domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableFundamentalDomain.lean#L25-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableFundamentalDomain.lean#L25-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMeasurableFundamentalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MeasurableFundamentalDomain
open Set Topology

theorem GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by sorry
