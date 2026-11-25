-- Prove2me | Theorems.Thm_GroundTheory_LocalField_summable_logSeries
-- name    : GroundTheory.LocalField.summable_logSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:14.677802+00:00
-- url     : https://prove2.me/theorems/16dce1b4-b4cd-43f1-bad9-8174d7f37e1c
-- title:
--   Local Field: summable log Series
-- statement:
--   The Local Field construction uses the summable log Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L226-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L226-L239

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
include p

theorem GroundTheory.LocalField.summable_logSeries {x : K} (hx : x ∈ valBall K 1) :
    Summable fun k : ℕ ↦ (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) := by sorry
