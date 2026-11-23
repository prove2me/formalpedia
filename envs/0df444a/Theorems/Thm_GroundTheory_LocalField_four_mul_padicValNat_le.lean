-- Prove2me | Theorems.Thm_GroundTheory_LocalField_four_mul_padicValNat_le
-- name    : GroundTheory.LocalField.four_mul_padicValNat_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:13.723577+00:00
-- url     : https://prove2.me/theorems/e2237435-0f0f-4564-9c06-a8718af14dcc
-- title:
--   Local Field: four mul padic Val Nat le
-- statement:
--   The Local Field construction uses the four mul padic Val Nat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L120-L129

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

theorem GroundTheory.LocalField.four_mul_padicValNat_le (p : ℕ) [hp : Fact p.Prime] (c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    4 * c * padicValNat p n ≤ n + 32 * c ^ 2 := by sorry
