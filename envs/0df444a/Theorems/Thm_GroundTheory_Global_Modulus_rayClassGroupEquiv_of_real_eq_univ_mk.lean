-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_rayClassGroupEquiv_of_real_eq_univ_mk
-- name    : GroundTheory.Global.Modulus.rayClassGroupEquiv_of_real_eq_univ_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:50.797821+00:00
-- url     : https://prove2.me/theorems/9b996e6c-3fc4-5ccb-bc95-9b69fc8c7f10
-- title:
--   Modulus: ray Class Group Equiv of real eq univ mk
-- statement:
--   The Modulus construction uses the ray Class Group Equiv of real eq univ mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L97-L100

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

theorem GroundTheory.Global.Modulus.rayClassGroupEquiv_of_real_eq_univ_mk (h : 𝔪.real = Set.univ) (x : IdeleGroup K) :
    𝔪.rayClassGroupEquiv_of_real_eq_univ h (QuotientGroup.mk x) =
      (QuotientGroup.mk x : _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal) := by sorry

attribute [defeq] GroundTheory.Global.Modulus.rayClassGroupEquiv_of_real_eq_univ_mk
