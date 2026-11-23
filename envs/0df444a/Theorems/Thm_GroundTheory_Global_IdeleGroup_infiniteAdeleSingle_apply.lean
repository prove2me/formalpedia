-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteAdeleSingle_apply
-- name    : GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:39.712356+00:00
-- url     : https://prove2.me/theorems/7778ca25-0c9e-4c70-84c5-12d648e3b2fb
-- title:
--   Idele Group: infinite Adele Single apply
-- statement:
--   The Idele Group construction uses the infinite Adele Single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L199-L201

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
omit [NumberField K]
open Classical

theorem GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply (w u : InfinitePlace K) (x : w.Completion) :
    infiniteAdeleSingle w x u = Pi.mulSingle (M := fun u : InfinitePlace K ↦ u.Completion) w x u := by sorry
