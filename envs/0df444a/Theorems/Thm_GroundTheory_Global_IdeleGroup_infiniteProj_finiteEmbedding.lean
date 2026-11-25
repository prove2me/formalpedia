-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_finiteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.infiniteProj_finiteEmbedding
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:23.533302+00:00
-- url     : https://prove2.me/theorems/7d2399a1-0a63-44f9-87f5-75830cdf55de
-- title:
--   Idele Group: infinite Proj finite Embedding
-- statement:
--   The Idele Group construction uses the infinite Proj finite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L54-L56

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

theorem GroundTheory.Global.IdeleGroup.infiniteProj_finiteEmbedding (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : infiniteProj w (finiteEmbedding v x) = 1 := by sorry
