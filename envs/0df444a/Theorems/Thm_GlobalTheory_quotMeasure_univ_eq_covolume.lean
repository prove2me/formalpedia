-- Prove2me | Theorems.Thm_GlobalTheory_quotMeasure_univ_eq_covolume
-- name    : GlobalTheory.quotMeasure_univ_eq_covolume
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:29.016739+00:00
-- url     : https://prove2.me/theorems/f10f136a-6766-4e51-adeb-6952ca7f57d3
-- title:
--   Global Theory: quot Measure univ eq covolume
-- statement:
--   The Global Theory construction uses the quot Measure univ eq covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L435-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L435-L438

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

theorem GlobalTheory.quotMeasure_univ_eq_covolume [h : HasFundamentalDomain G X μ] :
    quotMeasure G μ univ = covolume G X μ := by sorry
