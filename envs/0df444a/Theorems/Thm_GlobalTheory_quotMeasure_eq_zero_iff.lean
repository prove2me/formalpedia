-- Prove2me | Theorems.Thm_GlobalTheory_quotMeasure_eq_zero_iff
-- name    : GlobalTheory.quotMeasure_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:58.05917+00:00
-- url     : https://prove2.me/theorems/3cb6e81f-9485-4178-9471-439d2c7a83f4
-- title:
--   Global Theory: quot Measure eq zero iff
-- statement:
--   The Global Theory construction uses the quot Measure eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L553-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L553-L556

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
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}

theorem GlobalTheory.quotMeasure_eq_zero_iff [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    [SMulInvariantMeasure G X μ] : quotMeasure G μ = 0 ↔ μ = 0 := by sorry
