-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteProj
-- name    : GroundTheory.Global.IdeleGroup.continuous_finiteProj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:44.083887+00:00
-- url     : https://prove2.me/theorems/0e0acaf2-97ae-4336-b261-7bbc6201b9e4
-- title:
--   Idele Group: continuous finite Proj
-- statement:
--   The Idele Group construction uses the continuous finite Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L165-L167

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

theorem GroundTheory.Global.IdeleGroup.continuous_finiteProj (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteProj (K := K) v) := by sorry
