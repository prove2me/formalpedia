-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_finiteIndex_map_congruenceSubgroup
-- name    : GroundTheory.Global.Modulus.finiteIndex_map_congruenceSubgroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:07.125666+00:00
-- url     : https://prove2.me/theorems/9631a6cd-7fd6-4435-84c6-02c7510fe369
-- title:
--   Modulus: finite Index map congruence Subgroup
-- statement:
--   The Modulus construction uses the finite Index map congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L112-L116

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)

theorem GroundTheory.Global.Modulus.finiteIndex_map_congruenceSubgroup :
    (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).FiniteIndex := by sorry
