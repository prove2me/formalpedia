-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_sPresentation_apply
-- name    : GroundTheory.ProfCoh.sPresentation_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:47.998417+00:00
-- url     : https://prove2.me/theorems/53448e78-e3ef-5715-b36b-60eb8bf8354e
-- title:
--   Prof Coh: s Presentation apply
-- statement:
--   The Prof Coh construction uses the s Presentation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean#L129-L133

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

theorem GroundTheory.ProfCoh.sPresentation_apply [Finite S] (a : ∀ w : S, (w.1.adicCompletion K)ˣ)
    (D : Multiplicative (sDivisor S)) :
    sPresentation S (a, D) =
      SIdeleClassGroup.mk S (placesIdele S a * Additive.toMul (divisorIdele S D.toAdd)) := by sorry
