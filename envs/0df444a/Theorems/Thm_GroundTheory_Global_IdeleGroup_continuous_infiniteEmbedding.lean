-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:04.564071+00:00
-- url     : https://prove2.me/theorems/dc90cc23-a520-4d7e-aa40-56b8247e6ce0
-- title:
--   Idele Group: continuous infinite Embedding
-- statement:
--   The Idele Group construction uses the continuous infinite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L229-L231

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

theorem GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding (w : InfinitePlace K) :
    Continuous (infiniteEmbedding (K := K) w) := by sorry
