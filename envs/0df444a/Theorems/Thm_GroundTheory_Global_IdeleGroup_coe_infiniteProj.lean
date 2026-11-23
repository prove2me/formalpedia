-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
-- name    : GroundTheory.Global.IdeleGroup.coe_infiniteProj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:43.403718+00:00
-- url     : https://prove2.me/theorems/f308d553-d621-4f1b-8a60-4798e734d7ec
-- title:
--   Idele Group: coe infinite Proj
-- statement:
--   The Idele Group construction uses the coe infinite Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L225-L227

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

theorem GroundTheory.Global.IdeleGroup.coe_infiniteProj (w : InfinitePlace K) (x : IdeleGroup K) :
    ((infiniteProj w x : (w.Completion)ˣ) : w.Completion) = (x : 𝔸[K]).1 w := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_infiniteProj
