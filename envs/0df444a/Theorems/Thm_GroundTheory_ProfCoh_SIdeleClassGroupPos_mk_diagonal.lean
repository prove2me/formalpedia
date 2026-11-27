-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroupPos_mk_diagonal
-- name    : GroundTheory.ProfCoh.SIdeleClassGroupPos.mk_diagonal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:31.589807+00:00
-- url     : https://prove2.me/theorems/7f609fbd-a361-4e7b-8a86-3c825ff64049
-- title:
--   SIdele Class Group Pos: mk diagonal
-- statement:
--   The SIdele Class Group Pos construction uses the mk diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L78-L79

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal

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

theorem GroundTheory.ProfCoh.SIdeleClassGroupPos.mk_diagonal (a : Kˣ) : mk S (diagonal K a) = 1 := by sorry
