-- Prove2me | Theorems.Thm_GroundTheory_LocalField_summable_of_tendsto_zero
-- name    : GroundTheory.LocalField.summable_of_tendsto_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:39.451511+00:00
-- url     : https://prove2.me/theorems/711e53c7-cc7f-4418-9fb3-a1c26504722e
-- title:
--   Local Field: summable of tendsto zero
-- statement:
--   The Local Field construction uses the summable of tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L95-L98

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

theorem GroundTheory.LocalField.summable_of_tendsto_zero {f : ℕ → K} (hf : Tendsto f atTop (𝓝 0)) : Summable f := by sorry
