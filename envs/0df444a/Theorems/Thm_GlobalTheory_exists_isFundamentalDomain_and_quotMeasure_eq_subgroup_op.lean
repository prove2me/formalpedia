-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_and_quotMeasure_eq_subgroup_op
-- name    : GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq_subgroup_op
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:12.404467+00:00
-- url     : https://prove2.me/theorems/d71be7ee-59db-46ea-8359-dea52acca614
-- title:
--   Global Theory: exists is Fundamental Domain and quot Measure eq subgroup op
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain and quot Measure eq subgroup op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L653-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L653-L660

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

theorem GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq_subgroup_op (μ : Measure G)
    [μ.IsMulRightInvariant] :
    (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ.op D μ) ∧
      ∀ D : Set G, IsFundamentalDomain Γ.op D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel Γ.op G)) = quotMeasure Γ.op μ := by sorry
