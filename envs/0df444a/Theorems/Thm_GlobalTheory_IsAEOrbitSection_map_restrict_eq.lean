-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_map_restrict_eq
-- name    : GlobalTheory.IsAEOrbitSection.map_restrict_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:28.7765+00:00
-- url     : https://prove2.me/theorems/74fa7dcc-b91d-4808-867d-37cbc0f17886
-- title:
--   Is AEOrbit Section: map restrict eq
-- statement:
--   The Is AEOrbit Section construction uses the map restrict eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L321-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L321-L324

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

theorem GlobalTheory.IsAEOrbitSection.map_restrict_eq (hD : IsAEOrbitSection G D μ) (hD' : IsAEOrbitSection G D' μ) :
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) =
      (μ.restrict D').map (Quotient.mk (MulAction.orbitRel G X)) := by sorry
