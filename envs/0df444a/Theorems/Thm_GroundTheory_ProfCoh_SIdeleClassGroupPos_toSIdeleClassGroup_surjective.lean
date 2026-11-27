-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroupPos_toSIdeleClassGroup_surjective
-- name    : GroundTheory.ProfCoh.SIdeleClassGroupPos.toSIdeleClassGroup_surjective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:17:20.161612+00:00
-- url     : https://prove2.me/theorems/39590d59-3d66-4f8a-8d5a-a310fa74ba0f
-- title:
--   SIdele Class Group Pos: to SIdele Class Group surjective
-- statement:
--   The SIdele Class Group Pos construction uses the to SIdele Class Group surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L87-L89

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
open GroundTheory.ProfCoh.SIdeleClassGroupPos

theorem GroundTheory.ProfCoh.SIdeleClassGroupPos.toSIdeleClassGroup_surjective : Function.Surjective (toSIdeleClassGroup S) := by sorry
