-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_unitsOutsidePos
-- name    : GroundTheory.ProfCoh.mem_unitsOutsidePos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:51.516714+00:00
-- url     : https://prove2.me/theorems/9e1ca03a-7d72-5837-bb25-56a404802933
-- title:
--   Prof Coh: mem units Outside Pos
-- statement:
--   The Prof Coh construction uses the mem units Outside Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L30-L36

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

theorem GroundTheory.ProfCoh.mem_unitsOutsidePos {x : IdeleGroup K} :
    x ∈ unitsOutsidePos S ↔
      x ∈ unitsOutside S ∧ ∀ w : {w : InfinitePlace K // w.IsReal},
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by sorry
