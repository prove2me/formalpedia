-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply_eq_zero_iff
-- name    : GlobalTheory.IsAEOrbitSection.quotMeasure_apply_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:07.268432+00:00
-- url     : https://prove2.me/theorems/73fa2e57-4a3b-4374-af08-f2fe058850a7
-- title:
--   Is AEOrbit Section: quot Measure apply eq zero iff
-- statement:
--   The Is AEOrbit Section construction uses the quot Measure apply eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L368-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L368-L383

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

theorem GlobalTheory.IsAEOrbitSection.quotMeasure_apply_eq_zero_iff (hD : IsAEOrbitSection G D μ)
    {U : Set (Quotient (MulAction.orbitRel G X))} (hU : MeasurableSet U) :
    quotMeasure G μ U = 0 ↔ μ (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) = 0 := by sorry
