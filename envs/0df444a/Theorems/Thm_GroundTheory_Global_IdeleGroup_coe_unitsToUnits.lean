-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
-- name    : GroundTheory.Global.IdeleGroup.coe_unitsToUnits
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:13.588315+00:00
-- url     : https://prove2.me/theorems/f7081f22-10f3-429a-b9c1-5b5808f49e6a
-- title:
--   Idele Group: coe units To Units
-- statement:
--   The Idele Group construction uses the coe units To Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L105-L106

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
omit [NumberField K]

theorem GroundTheory.Global.IdeleGroup.coe_unitsToUnits (u : (𝓞 K)ˣ) : ((unitsToUnits K u : Kˣ) : K) = ((u : 𝓞 K) : K) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
