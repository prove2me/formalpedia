-- Prove2me | Theorems.Thm_GlobalTheory_hasFundamentalDomain_subgroup_op
-- name    : GlobalTheory.hasFundamentalDomain_subgroup_op
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:58.553426+00:00
-- url     : https://prove2.me/theorems/15d4c41e-f4ef-4ad8-a26b-972d77b31fde
-- title:
--   Global Theory: has Fundamental Domain subgroup op
-- statement:
--   The Global Theory construction uses the has Fundamental Domain subgroup op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L636-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L636-L638

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

theorem GlobalTheory.hasFundamentalDomain_subgroup_op (μ : Measure G) : HasFundamentalDomain Γ.op G μ := by sorry
