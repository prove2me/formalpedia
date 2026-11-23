-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_iff
-- name    : GroundTheory.LocalField.mem_unitFiltrationUnits_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:55.324647+00:00
-- url     : https://prove2.me/theorems/4b7f7733-3589-485f-abc1-b404b47aa918
-- title:
--   Local Field: mem unit Filtration Units iff
-- statement:
--   The Local Field construction uses the mem unit Filtration Units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L25-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L25-L47

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

theorem GroundTheory.LocalField.mem_unitFiltrationUnits_iff {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by sorry
