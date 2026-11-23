-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
-- name    : GroundTheory.Global.IdeleClassGroup.continuous_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:24.446465+00:00
-- url     : https://prove2.me/theorems/1b8d913d-be82-453a-85ba-a7a88a37c360
-- title:
--   Idele Class Group: continuous mk
-- statement:
--   The Idele Class Group construction uses the continuous mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L75-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L75-L75

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

theorem GroundTheory.Global.IdeleClassGroup.continuous_mk : Continuous (mk K) := by sorry
