-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_pow_lt
-- name    : GroundTheory.LocalField.exists_pow_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:33.950619+00:00
-- url     : https://prove2.me/theorems/79db0fde-a8ce-448b-b30f-021c0a40b8e0
-- title:
--   Local Field: exists pow lt
-- statement:
--   The Local Field construction uses the exists pow lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L148-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L148-L157

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

theorem GroundTheory.LocalField.exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by sorry
