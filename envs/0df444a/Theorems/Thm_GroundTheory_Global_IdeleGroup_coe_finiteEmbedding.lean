-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:42.165086+00:00
-- url     : https://prove2.me/theorems/009b9787-44fb-41ca-9ece-3f2d271d4e4a
-- title:
--   Idele Group: coe finite Embedding
-- statement:
--   The Idele Group construction uses the coe finite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L151-L154

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

theorem GroundTheory.Global.IdeleGroup.coe_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((finiteEmbedding v x : IdeleGroup K) : 𝔸[K]) =
      (1, finiteAdeleSingle v (x : v.adicCompletion K)) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
