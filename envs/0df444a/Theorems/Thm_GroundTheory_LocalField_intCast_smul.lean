-- Prove2me | Theorems.Thm_GroundTheory_LocalField_intCast_smul
-- name    : GroundTheory.LocalField.intCast_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:55.441853+00:00
-- url     : https://prove2.me/theorems/40c71507-a968-470d-84b2-c027fc68efb9
-- title:
--   Local Field: int Cast smul
-- statement:
--   The Local Field construction uses the int Cast smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsModule.lean#L303-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsModule.lean#L303-L305

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
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
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

theorem GroundTheory.LocalField.intCast_smul (c : ℤ) (u : Additive (unitFiltrationUnits K 1)) :
    ((c : ℤ_[p])) • u = c • u := by sorry
