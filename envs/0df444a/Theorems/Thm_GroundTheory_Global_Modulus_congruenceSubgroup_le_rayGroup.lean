-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_le_rayGroup
-- name    : GroundTheory.Global.Modulus.congruenceSubgroup_le_rayGroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:40.147808+00:00
-- url     : https://prove2.me/theorems/72d5a14b-5901-5d32-8049-479d7fd39e1e
-- title:
--   Modulus: congruence Subgroup le ray Group
-- statement:
--   The Modulus construction uses the congruence Subgroup le ray Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L28-L29

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

theorem GroundTheory.Global.Modulus.congruenceSubgroup_le_rayGroup : 𝔪.congruenceSubgroup ≤ 𝔪.rayGroup := by sorry
