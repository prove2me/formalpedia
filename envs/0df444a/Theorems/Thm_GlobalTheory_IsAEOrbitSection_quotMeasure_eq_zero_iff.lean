-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_eq_zero_iff
-- name    : GlobalTheory.IsAEOrbitSection.quotMeasure_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:20.494078+00:00
-- url     : https://prove2.me/theorems/e5a54c61-fdba-405c-ae9b-b06fe651b65f
-- title:
--   Is AEOrbit Section: quot Measure eq zero iff
-- statement:
--   The Is AEOrbit Section construction uses the quot Measure eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L386-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L386-L388

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

theorem GlobalTheory.IsAEOrbitSection.quotMeasure_eq_zero_iff (hD : IsAEOrbitSection G D μ) : quotMeasure G μ = 0 ↔ μ = 0 := by sorry
