-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_unitsOutside
-- name    : GroundTheory.ProfCoh.mem_unitsOutside
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:10.325082+00:00
-- url     : https://prove2.me/theorems/e1e66a45-367e-4b6a-998c-82a8c24deaf7
-- title:
--   Prof Coh: mem units Outside
-- statement:
--   The Prof Coh construction uses the mem units Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
variable {S}

theorem GroundTheory.ProfCoh.mem_unitsOutside {x : IdeleGroup K} :
    x ∈ unitsOutside S ↔
      (∀ v ∈ S, finiteProj v x = 1) ∧ ∀ v ∉ S, finiteProj v x ∈ unitsLevel v 0 := by sorry
