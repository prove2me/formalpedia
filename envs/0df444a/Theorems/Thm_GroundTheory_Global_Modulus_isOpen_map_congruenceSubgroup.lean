-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_isOpen_map_congruenceSubgroup
-- name    : GroundTheory.Global.Modulus.isOpen_map_congruenceSubgroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:57.948809+00:00
-- url     : https://prove2.me/theorems/bd3a4455-2504-5ba4-b504-853595fbcfd7
-- title:
--   Modulus: is Open map congruence Subgroup
-- statement:
--   The Modulus construction uses the is Open map congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L103-L106

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
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

theorem GroundTheory.Global.Modulus.isOpen_map_congruenceSubgroup (𝔪 : Modulus K) :
    IsOpen (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) : Set (IdeleClassGroup K)) := by sorry
