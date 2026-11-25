-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ker_localQuotientMap
-- name    : GroundTheory.Global.IdeleGroup.ker_localQuotientMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:53.301073+00:00
-- url     : https://prove2.me/theorems/afbba18d-c52f-424b-8437-6adda07cd94c
-- title:
--   Idele Group: ker local Quotient Map
-- statement:
--   The Idele Group construction uses the ker local Quotient Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L99-L107

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

theorem GroundTheory.Global.IdeleGroup.ker_localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localQuotientMap T H H' S).ker =
      (localSubgroup S T H H').subgroupOf (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) := by sorry
