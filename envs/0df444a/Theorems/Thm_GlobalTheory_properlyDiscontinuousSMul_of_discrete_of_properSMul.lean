-- Prove2me | Theorems.Thm_GlobalTheory_properlyDiscontinuousSMul_of_discrete_of_properSMul
-- name    : GlobalTheory.properlyDiscontinuousSMul_of_discrete_of_properSMul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:05.474017+00:00
-- url     : https://prove2.me/theorems/f2301379-e2ea-552f-b667-f6196814090a
-- title:
--   Global Theory: properly Discontinuous SMul of discrete of proper SMul
-- statement:
--   The Global Theory construction uses the properly Discontinuous SMul of discrete of proper SMul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L664-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L664-L671

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

theorem GlobalTheory.properlyDiscontinuousSMul_of_discrete_of_properSMul {G X : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MulAction G X] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [ProperSMul G X] (Γ : Subgroup G) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ X := by sorry
