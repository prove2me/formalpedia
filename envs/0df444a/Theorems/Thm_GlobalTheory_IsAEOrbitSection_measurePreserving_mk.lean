-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_measurePreserving_mk
-- name    : GlobalTheory.IsAEOrbitSection.measurePreserving_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:09.983216+00:00
-- url     : https://prove2.me/theorems/e9a68e75-625e-4813-8c38-066456816261
-- title:
--   Is AEOrbit Section: measure Preserving mk
-- statement:
--   The Is AEOrbit Section construction uses the measure Preserving mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L327-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L327-L329

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

theorem GlobalTheory.IsAEOrbitSection.measurePreserving_mk (hD : IsAEOrbitSection G D μ) :
    MeasurePreserving (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict D) (quotMeasure G μ) := by sorry
