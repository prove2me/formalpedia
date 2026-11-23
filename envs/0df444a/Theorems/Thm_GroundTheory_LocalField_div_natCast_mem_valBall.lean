-- Prove2me | Theorems.Thm_GroundTheory_LocalField_div_natCast_mem_valBall
-- name    : GroundTheory.LocalField.div_natCast_mem_valBall
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:01.083044+00:00
-- url     : https://prove2.me/theorems/14e63902-070e-4d9f-9c6d-d9a00da08a00
-- title:
--   Local Field: div nat Cast mem val Ball
-- statement:
--   The Local Field construction uses the div nat Cast mem val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L189-L193

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

theorem GroundTheory.LocalField.div_natCast_mem_valBall {a : ℤ} {x : K} (hx : x ∈ valBall K a) {n : ℕ} (hn : n ≠ 0) :
    x / n ∈ valBall K (a - absRamificationIndex K * padicValNat p n) := by sorry
