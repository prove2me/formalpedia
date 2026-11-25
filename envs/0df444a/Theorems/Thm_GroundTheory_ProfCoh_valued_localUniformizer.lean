-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_valued_localUniformizer
-- name    : GroundTheory.ProfCoh.valued_localUniformizer
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:17.449144+00:00
-- url     : https://prove2.me/theorems/4674ca1d-7411-588c-814e-bb529d6da982
-- title:
--   Prof Coh: valued local Uniformizer
-- statement:
--   The Prof Coh construction uses the valued local Uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L101-L105

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

theorem GroundTheory.ProfCoh.valued_localUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((localUniformizer v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by sorry
