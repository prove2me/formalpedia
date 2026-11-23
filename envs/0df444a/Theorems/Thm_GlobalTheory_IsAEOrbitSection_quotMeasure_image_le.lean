-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_image_le
-- name    : GlobalTheory.IsAEOrbitSection.quotMeasure_image_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.421842+00:00
-- url     : https://prove2.me/theorems/9b8fa208-632a-436a-9d4e-7c776fa83264
-- title:
--   Is AEOrbit Section: quot Measure image le
-- statement:
--   The Is AEOrbit Section construction uses the quot Measure image le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L392-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L392-L408

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

theorem GlobalTheory.IsAEOrbitSection.quotMeasure_image_le (hD : IsAEOrbitSection G D μ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (Quotient.mk (MulAction.orbitRel G X) '' A) ∧
      quotMeasure G μ (Quotient.mk (MulAction.orbitRel G X) '' A) ≤ μ A := by sorry
