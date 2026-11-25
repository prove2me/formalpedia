-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroupPos_mk_surjective
-- name    : GroundTheory.ProfCoh.SIdeleClassGroupPos.mk_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:55.185802+00:00
-- url     : https://prove2.me/theorems/49d7ec22-9438-47b1-9b6c-9d1228501203
-- title:
--   SIdele Class Group Pos: mk surjective
-- statement:
--   The SIdele Class Group Pos construction uses the mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L76-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L76-L76

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective

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

theorem GroundTheory.ProfCoh.SIdeleClassGroupPos.mk_surjective : Function.Surjective (mk S) := by sorry
