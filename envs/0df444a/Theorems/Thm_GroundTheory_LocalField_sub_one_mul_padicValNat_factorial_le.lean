-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sub_one_mul_padicValNat_factorial_le
-- name    : GroundTheory.LocalField.sub_one_mul_padicValNat_factorial_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:45.364654+00:00
-- url     : https://prove2.me/theorems/f1bd98db-d388-4cf3-bd4c-3d90dfffb532
-- title:
--   Local Field: sub one mul padic Val Nat factorial le
-- statement:
--   The Local Field construction uses the sub one mul padic Val Nat factorial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L220-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L220-L222

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
omit [CharP 𝓀[K] p] [CharZero K]

theorem GroundTheory.LocalField.sub_one_mul_padicValNat_factorial_le (k : ℕ) :
    (p - 1) * padicValNat p k.factorial ≤ k := by sorry
