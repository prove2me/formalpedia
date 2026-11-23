-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteProj
-- name    : GroundTheory.Global.IdeleGroup.continuous_infiniteProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:27.736321+00:00
-- url     : https://prove2.me/theorems/e2361ab1-ca29-4052-9f48-25489799a619
-- title:
--   Idele Group: continuous infinite Proj
-- statement:
--   The Idele Group construction uses the continuous infinite Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L233-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L233-L235

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

theorem GroundTheory.Global.IdeleGroup.continuous_infiniteProj (w : InfinitePlace K) :
    Continuous (infiniteProj (K := K) w) := by sorry
