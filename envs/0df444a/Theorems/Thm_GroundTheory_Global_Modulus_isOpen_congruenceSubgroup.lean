-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_isOpen_congruenceSubgroup
-- name    : GroundTheory.Global.Modulus.isOpen_congruenceSubgroup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:51.627027+00:00
-- url     : https://prove2.me/theorems/a3007ceb-bcec-5808-ade8-d5843d27137c
-- title:
--   Modulus: is Open congruence Subgroup
-- statement:
--   The Modulus construction uses the is Open congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L120-L123

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

theorem GroundTheory.Global.Modulus.isOpen_congruenceSubgroup : IsOpen (𝔪.congruenceSubgroup : Set (IdeleGroup K)) := by sorry
