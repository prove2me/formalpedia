-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
-- name    : GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding_of_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:06.08733+00:00
-- url     : https://prove2.me/theorems/17b3c717-3f85-498d-8add-20b44d2d80fe
-- title:
--   Idele Group: finite Proj finite Embedding of ne
-- statement:
--   The Idele Group construction uses the finite Proj finite Embedding of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L175-L178

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

theorem GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteProj w (finiteEmbedding v x) = 1 := by sorry
