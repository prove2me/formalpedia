-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_integral_quotMeasure
-- name    : GlobalTheory.IsAEOrbitSection.integral_quotMeasure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:21.886799+00:00
-- url     : https://prove2.me/theorems/cff29f3c-c455-46e0-80ed-db03a180e1a1
-- title:
--   Is AEOrbit Section: integral quot Measure
-- statement:
--   The Is AEOrbit Section construction uses the integral quot Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L353-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L353-L358

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

theorem GlobalTheory.IsAEOrbitSection.integral_quotMeasure (hD : IsAEOrbitSection G D μ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Quotient (MulAction.orbitRel G X) → E}
    (hf : AEStronglyMeasurable f (quotMeasure G μ)) :
    ∫ q, f q ∂quotMeasure G μ = ∫ x in D, f (Quotient.mk _ x) ∂μ := by sorry
