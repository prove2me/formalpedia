-- Prove2me | Theorems.Thm_GroundTheory_LocalField_expSeries_sub_one_sub_self_mem
-- name    : GroundTheory.LocalField.expSeries_sub_one_sub_self_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:18.70558+00:00
-- url     : https://prove2.me/theorems/b9ab2325-e4ec-473f-891b-502304dab233
-- title:
--   Local Field: exp Series sub one sub self mem
-- statement:
--   The Local Field construction uses the exp Series sub one sub self mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L313-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L313-L337

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

theorem GroundTheory.LocalField.expSeries_sub_one_sub_self_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 - x ∈ valBall K (a + 1) := by sorry
