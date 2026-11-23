-- Prove2me | Theorems.Thm_GroundTheory_LocalField_pow_mem_valBall
-- name    : GroundTheory.LocalField.pow_mem_valBall
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:50.470243+00:00
-- url     : https://prove2.me/theorems/d245bf52-2df3-4f71-91ec-7e0f68b654af
-- title:
--   Local Field: pow mem val Ball
-- statement:
--   The Local Field construction uses the pow mem val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L41-L48

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

theorem GroundTheory.LocalField.pow_mem_valBall {n : ℤ} {x : K} (hx : x ∈ valBall K n) (k : ℕ) :
    x ^ k ∈ valBall K (k * n) := by sorry
