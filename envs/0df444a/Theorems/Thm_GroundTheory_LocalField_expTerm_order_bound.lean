-- Prove2me | Theorems.Thm_GroundTheory_LocalField_expTerm_order_bound
-- name    : GroundTheory.LocalField.expTerm_order_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:37.473523+00:00
-- url     : https://prove2.me/theorems/b596f880-2aad-4693-9243-746ead5ba56a
-- title:
--   Local Field: exp Term order bound
-- statement:
--   The Local Field construction uses the exp Term order bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L281-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L281-L296

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

theorem GroundTheory.LocalField.expTerm_order_bound {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a)
    (k : ℕ) : (k : ℤ) ≤ (p - 1 : ℤ) * (k * a - absRamificationIndex K * padicValNat p k.factorial)
    := by sorry
