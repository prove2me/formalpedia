-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_eq_inf
-- name    : GroundTheory.Global.Modulus.congruenceSubgroup_eq_inf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:49.537181+00:00
-- url     : https://prove2.me/theorems/6d9dd9d2-da1c-4156-aa19-04d6e9328913
-- title:
--   Modulus: congruence Subgroup eq inf
-- statement:
--   The Modulus construction uses the congruence Subgroup eq inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L141-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L141-L155

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)

theorem GroundTheory.Global.Modulus.congruenceSubgroup_eq_inf :
    𝔪.congruenceSubgroup = 𝔪.idelesOneMod ⊓ standardOpenSubgroup K := by sorry
