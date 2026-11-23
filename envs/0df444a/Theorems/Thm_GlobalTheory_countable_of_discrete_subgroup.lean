-- Prove2me | Theorems.Thm_GlobalTheory_countable_of_discrete_subgroup
-- name    : GlobalTheory.countable_of_discrete_subgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:33.595342+00:00
-- url     : https://prove2.me/theorems/3e0547ce-5e82-4f4f-ad73-42194c732bb7
-- title:
--   Global Theory: countable of discrete subgroup
-- statement:
--   The Global Theory construction uses the countable of discrete subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L567-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L567-L568

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

theorem GlobalTheory.countable_of_discrete_subgroup : Countable Γ := by sorry
