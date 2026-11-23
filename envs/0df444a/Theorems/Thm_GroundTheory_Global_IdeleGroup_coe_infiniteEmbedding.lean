-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:47.111635+00:00
-- url     : https://prove2.me/theorems/4e634c5c-ce24-4d8c-b7c1-46c7955a7aec
-- title:
--   Idele Group: coe infinite Embedding
-- statement:
--   The Idele Group construction uses the coe infinite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L219-L222

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

theorem GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((infiniteEmbedding w x : IdeleGroup K) : 𝔸[K]) =
      (infiniteAdeleSingle w (x : w.Completion), 1) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
