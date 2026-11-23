-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_isOpenMap_mk
-- name    : GroundTheory.Global.IdeleClassGroup.isOpenMap_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:29.511726+00:00
-- url     : https://prove2.me/theorems/2d1b56e0-3985-48f7-8ef2-17e7f8159fb6
-- title:
--   Idele Class Group: is Open Map mk
-- statement:
--   The Idele Class Group construction uses the is Open Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L77-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L77-L77

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
open GroundTheory.Global.IdeleClassGroup

theorem GroundTheory.Global.IdeleClassGroup.isOpenMap_mk : IsOpenMap (mk K) := by sorry
