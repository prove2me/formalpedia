-- Prove2me | Theorems.Thm_GroundTheory_LocalField_padicLog_smul
-- name    : GroundTheory.LocalField.padicLog_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:56:23.597582+00:00
-- url     : https://prove2.me/theorems/c8af74ad-75c9-4668-8fdd-b032326686db
-- title:
--   Local Field: padic Log smul
-- statement:
--   The Local Field construction uses the padic Log smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogLinear.lean#L42-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogLinear.lean#L42-L80

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
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

theorem GroundTheory.LocalField.padicLog_smul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (a • u) = CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u := by sorry
