-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_subgroup_op
-- name    : GlobalTheory.exists_isFundamentalDomain_subgroup_op
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:42.083017+00:00
-- url     : https://prove2.me/theorems/ea351516-afae-4179-818f-1169c13e4679
-- title:
--   Global Theory: exists is Fundamental Domain subgroup op
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain subgroup op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L612-L628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L612-L628

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

theorem GlobalTheory.exists_isFundamentalDomain_subgroup_op :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ.op, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by sorry
