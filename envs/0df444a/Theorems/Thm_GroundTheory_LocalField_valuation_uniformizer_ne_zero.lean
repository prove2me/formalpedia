-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valuation_uniformizer_ne_zero
-- name    : GroundTheory.LocalField.valuation_uniformizer_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:12.655248+00:00
-- url     : https://prove2.me/theorems/d83cdbde-eb56-4840-ad8f-47c621f619b1
-- title:
--   Local Field: valuation uniformizer ne zero
-- statement:
--   The Local Field construction uses the valuation uniformizer ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L108-L111

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

theorem GroundTheory.LocalField.valuation_uniformizer_ne_zero {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by sorry
