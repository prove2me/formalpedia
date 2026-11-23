-- Prove2me | Theorems.Thm_GroundTheory_LocalField_one_le_of_lt_sub_one_mul
-- name    : GroundTheory.LocalField.one_le_of_lt_sub_one_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:43.727206+00:00
-- url     : https://prove2.me/theorems/fc3dce07-b116-4494-8e68-86b6971130a3
-- title:
--   Local Field: one le of lt sub one mul
-- statement:
--   The Local Field construction uses the one le of lt sub one mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L241-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L241-L247

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

theorem GroundTheory.LocalField.one_le_of_lt_sub_one_mul {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    1 ≤ a := by sorry
