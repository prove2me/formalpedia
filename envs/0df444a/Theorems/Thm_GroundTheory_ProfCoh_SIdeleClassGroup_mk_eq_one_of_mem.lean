-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroup_mk_eq_one_of_mem
-- name    : GroundTheory.ProfCoh.SIdeleClassGroup.mk_eq_one_of_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:11.987784+00:00
-- url     : https://prove2.me/theorems/b9e97680-c72e-44dd-806c-91cd56d65f89
-- title:
--   SIdele Class Group: mk eq one of mem
-- statement:
--   The SIdele Class Group construction uses the mk eq one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L62-L63

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
open GroundTheory.ProfCoh.SIdeleClassGroup

theorem GroundTheory.ProfCoh.SIdeleClassGroup.mk_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ unitsOutside S) : mk S x = 1 := by sorry
