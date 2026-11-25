-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_quotientMapCongruenceEquiv_mk
-- name    : GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:13.044192+00:00
-- url     : https://prove2.me/theorems/d18e33e7-2810-49b0-9b4a-e0e321e4b85b
-- title:
--   Modulus: quotient Map Congruence Equiv mk
-- statement:
--   The Modulus construction uses the quotient Map Congruence Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/RayClass.lean#L46-L49

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

theorem GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk (x : IdeleGroup K) :
    𝔪.quotientMapCongruenceEquiv (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      (QuotientGroup.mk x : 𝔪.RayClassGroup) := by sorry

attribute [defeq] GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk
