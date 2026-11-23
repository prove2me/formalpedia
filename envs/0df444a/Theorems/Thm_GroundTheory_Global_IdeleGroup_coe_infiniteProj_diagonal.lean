-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
-- name    : GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:15.184165+00:00
-- url     : https://prove2.me/theorems/cb992bd4-3b03-4a51-8450-6a087df5b348
-- title:
--   Idele Group: coe infinite Proj diagonal
-- statement:
--   The Idele Group construction uses the coe infinite Proj diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L251-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L251-L254

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

theorem GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal (w : InfinitePlace K) (x : Kˣ) :
    ((infiniteProj w (diagonal K x) : (w.Completion)ˣ) : w.Completion) =
      ((x : K) : w.Completion) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
