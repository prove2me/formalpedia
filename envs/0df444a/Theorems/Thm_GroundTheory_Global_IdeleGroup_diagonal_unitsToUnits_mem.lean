-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_unitsToUnits_mem
-- name    : GroundTheory.Global.IdeleGroup.diagonal_unitsToUnits_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:40.156159+00:00
-- url     : https://prove2.me/theorems/b187b411-20d1-442d-a67a-dbf02f9b4e0c
-- title:
--   Idele Group: diagonal units To Units mem
-- statement:
--   The Idele Group construction uses the diagonal units To Units mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L108-L116

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.diagonal_unitsToUnits_mem (u : (𝓞 K)ˣ) :
    diagonal K (unitsToUnits K u) ∈ standardOpenSubgroup K := by sorry
