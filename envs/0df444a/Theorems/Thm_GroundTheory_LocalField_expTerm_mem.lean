-- Prove2me | Theorems.Thm_GroundTheory_LocalField_expTerm_mem
-- name    : GroundTheory.LocalField.expTerm_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:08.076418+00:00
-- url     : https://prove2.me/theorems/47e4febf-c771-41bb-b846-c189c1c1241b
-- title:
--   Local Field: exp Term mem
-- statement:
--   The Local Field construction uses the exp Term mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L214-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L214-L217

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

theorem GroundTheory.LocalField.expTerm_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    x ^ k / (k.factorial : K) ∈
      valBall K (k * a - absRamificationIndex K * padicValNat p k.factorial) := by sorry
