-- Prove2me | Theorems.Thm_GroundTheory_LocalField_val_image_unitFiltrationUnits
-- name    : GroundTheory.LocalField.val_image_unitFiltrationUnits
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:52.828814+00:00
-- url     : https://prove2.me/theorems/11ffd8d1-f291-47fd-9794-9ce5a7024da5
-- title:
--   Local Field: val image unit Filtration Units
-- statement:
--   The Local Field construction uses the val image unit Filtration Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L91-L106

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.val_image_unitFiltrationUnits {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by sorry
