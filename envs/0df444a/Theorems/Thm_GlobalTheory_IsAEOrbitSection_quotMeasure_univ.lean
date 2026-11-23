-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_univ
-- name    : GlobalTheory.IsAEOrbitSection.quotMeasure_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:16.579887+00:00
-- url     : https://prove2.me/theorems/71f80dae-ef60-4e6d-8b1b-65c9d4b49d95
-- title:
--   Is AEOrbit Section: quot Measure univ
-- statement:
--   The Is AEOrbit Section construction uses the quot Measure univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L338-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L338-L339

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
open GlobalTheory.IsAEOrbitSection
variable {D D' : Set X}

theorem GlobalTheory.IsAEOrbitSection.quotMeasure_univ (hD : IsAEOrbitSection G D μ) : quotMeasure G μ univ = μ D := by sorry
