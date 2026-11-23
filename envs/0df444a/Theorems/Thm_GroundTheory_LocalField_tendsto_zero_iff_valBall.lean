-- Prove2me | Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
-- name    : GroundTheory.LocalField.tendsto_zero_iff_valBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:08.227384+00:00
-- url     : https://prove2.me/theorems/2e2d9aaf-dfb3-4c6b-81bf-0c996d7833a2
-- title:
--   Local Field: tendsto zero iff val Ball
-- statement:
--   The Local Field construction uses the tendsto zero iff val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L79-L93

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

theorem GroundTheory.LocalField.tendsto_zero_iff_valBall {ι : Type*} {l : Filter ι} {f : ι → K} :
    Tendsto f l (𝓝 0) ↔ ∀ N : ℤ, ∀ᶠ i in l, f i ∈ valBall K N := by sorry
