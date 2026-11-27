-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_exists_map_congruenceSubgroup_le_of_finiteIndex
-- name    : GroundTheory.Global.IdeleClassGroup.exists_map_congruenceSubgroup_le_of_finiteIndex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:16.900813+00:00
-- url     : https://prove2.me/theorems/4f62bb94-b07e-57fe-92fc-dab3a1891850
-- title:
--   Idele Class Group: exists map congruence Subgroup le of finite Index
-- statement:
--   The Idele Class Group construction uses the exists map congruence Subgroup le of finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L97-L101

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

theorem GroundTheory.Global.IdeleClassGroup.exists_map_congruenceSubgroup_le_of_finiteIndex
    (H : Subgroup (IdeleClassGroup K)) (hH : IsOpen (H : Set (IdeleClassGroup K)))
    (_ : H.FiniteIndex) :
    ∃ 𝔪 : Modulus K, 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H := by sorry
