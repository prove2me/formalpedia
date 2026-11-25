-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_mem_congruenceSubgroup_iff
-- name    : GroundTheory.Global.Modulus.mem_congruenceSubgroup_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:53.419589+00:00
-- url     : https://prove2.me/theorems/6a2c6734-bca7-56cb-a46c-88aa42d0e323
-- title:
--   Modulus: mem congruence Subgroup iff
-- statement:
--   The Modulus construction uses the mem congruence Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L100-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L100-L118

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

theorem GroundTheory.Global.Modulus.mem_congruenceSubgroup_iff {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal →
          Valued.v ((x : 𝔸[K]).2 v - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        (∀ v, ¬ v.asIdeal ∣ 𝔪.ideal → Valued.v ((x : 𝔸[K]).2 v) = 1) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((x : 𝔸[K]).1 w.1) := by sorry
