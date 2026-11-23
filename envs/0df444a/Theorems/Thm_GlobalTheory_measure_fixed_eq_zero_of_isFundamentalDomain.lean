-- Prove2me | Theorems.Thm_GlobalTheory_measure_fixed_eq_zero_of_isFundamentalDomain
-- name    : GlobalTheory.measure_fixed_eq_zero_of_isFundamentalDomain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:19.90216+00:00
-- url     : https://prove2.me/theorems/e339df8f-2548-488f-bb33-f617d62438d7
-- title:
--   Global Theory: measure fixed eq zero of is Fundamental Domain
-- statement:
--   The Global Theory construction uses the measure fixed eq zero of is Fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L260-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L260-L272

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

theorem GlobalTheory.measure_fixed_eq_zero_of_isFundamentalDomain {D : Set X} (hD : IsFundamentalDomain G D μ)
    {g : G} (hg : g ≠ 1) : μ {x | g • x = x} = 0 := by sorry
