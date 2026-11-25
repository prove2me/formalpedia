-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_le_standardOpenSubgroup
-- name    : GroundTheory.Global.Modulus.congruenceSubgroup_le_standardOpenSubgroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:02.557818+00:00
-- url     : https://prove2.me/theorems/d9e8a5b6-9c0d-4b40-8822-9c9cf19083c1
-- title:
--   Modulus: congruence Subgroup le standard Open Subgroup
-- statement:
--   The Modulus construction uses the congruence Subgroup le standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L125-L128

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

theorem GroundTheory.Global.Modulus.congruenceSubgroup_le_standardOpenSubgroup :
    𝔪.congruenceSubgroup ≤ standardOpenSubgroup K := by sorry
