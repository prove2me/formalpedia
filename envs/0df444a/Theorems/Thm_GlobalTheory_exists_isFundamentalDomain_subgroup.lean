-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_subgroup
-- name    : GlobalTheory.exists_isFundamentalDomain_subgroup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:55.259831+00:00
-- url     : https://prove2.me/theorems/fe54b6cf-5712-4d95-8b75-abb3f6810c91
-- title:
--   Global Theory: exists is Fundamental Domain subgroup
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L582-L608
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L582-L608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
variable [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.exists_isFundamentalDomain_subgroup :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ D μ := by sorry
