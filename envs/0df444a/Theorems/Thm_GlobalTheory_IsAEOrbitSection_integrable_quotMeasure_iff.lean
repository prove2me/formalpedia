-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_integrable_quotMeasure_iff
-- name    : GlobalTheory.IsAEOrbitSection.integrable_quotMeasure_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:18.250014+00:00
-- url     : https://prove2.me/theorems/a114bab4-5b21-4451-8bac-a3b8e7a9648b
-- title:
--   Is AEOrbit Section: integrable quot Measure iff
-- statement:
--   The Is AEOrbit Section construction uses the integrable quot Measure iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L361-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L361-L364

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

theorem GlobalTheory.IsAEOrbitSection.integrable_quotMeasure_iff (hD : IsAEOrbitSection G D μ) {E : Type*} [NormedAddCommGroup E]
    {f : Quotient (MulAction.orbitRel G X) → E} (hf : AEStronglyMeasurable f (quotMeasure G μ)) :
    Integrable f (quotMeasure G μ) ↔ IntegrableOn (fun x => f (Quotient.mk _ x)) D μ := by sorry
