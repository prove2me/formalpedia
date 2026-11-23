-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteAdeleSingle
-- name    : GroundTheory.Global.IdeleGroup.continuous_finiteAdeleSingle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:30.312841+00:00
-- url     : https://prove2.me/theorems/a907a7a2-18bc-49d7-aa42-3ad624b8c8d7
-- title:
--   Idele Group: continuous finite Adele Single
-- statement:
--   The Idele Group construction uses the continuous finite Adele Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L122-L138

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}

theorem GroundTheory.Global.IdeleGroup.continuous_finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleSingle (K := K) v) := by sorry
