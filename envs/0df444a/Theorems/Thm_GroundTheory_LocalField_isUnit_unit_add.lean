-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnit_unit_add
-- name    : GroundTheory.LocalField.isUnit_unit_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:20.326448+00:00
-- url     : https://prove2.me/theorems/6b846280-1660-4cd3-8270-adb5b8ce1156
-- title:
--   Local Field: is Unit unit add
-- statement:
--   The Local Field construction uses the is Unit unit add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L19-L26

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

theorem GroundTheory.LocalField.isUnit_unit_add {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by sorry
