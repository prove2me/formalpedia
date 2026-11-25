-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_localQuotientMap_surjective
-- name    : GroundTheory.Global.IdeleGroup.localQuotientMap_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:37.921661+00:00
-- url     : https://prove2.me/theorems/6ba3e70b-2ec0-4eb6-8f3d-f42525ac91eb
-- title:
--   Idele Group: local Quotient Map surjective
-- statement:
--   The Idele Group construction uses the local Quotient Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L109-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L109-L135

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)

theorem GroundTheory.Global.IdeleGroup.localQuotientMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localQuotientMap T H H' S) := by sorry
