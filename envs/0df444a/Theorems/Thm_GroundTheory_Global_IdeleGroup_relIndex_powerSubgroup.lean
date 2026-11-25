-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_relIndex_powerSubgroup
-- name    : GroundTheory.Global.IdeleGroup.relIndex_powerSubgroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:14:03.517537+00:00
-- url     : https://prove2.me/theorems/2be162d3-3df2-4f97-a46c-4aed730952f5
-- title:
--   Idele Group: rel Index power Subgroup
-- statement:
--   The Idele Group construction uses the rel Index power Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L154-L158

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

theorem GroundTheory.Global.IdeleGroup.relIndex_powerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by sorry
