-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_unitFiltration_le_range_pow
-- name    : GroundTheory.LocalField.exists_unitFiltration_le_range_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:30.230311+00:00
-- url     : https://prove2.me/theorems/5bf92e30-0d05-457e-b8ac-2c499cef9aa0
-- title:
--   Local Field: exists unit Filtration le range pow
-- statement:
--   The Local Field construction uses the exists unit Filtration le range pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L174-L182

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
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
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.exists_unitFiltration_le_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    ∃ N, unitFiltration K N ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by sorry
