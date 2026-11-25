-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.isOpen_standardOpenSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:30.429975+00:00
-- url     : https://prove2.me/theorems/1be57d9a-2658-4d08-af97-48af69be851e
-- title:
--   Idele Group: is Open standard Open Subgroup
-- statement:
--   The Idele Group construction uses the is Open standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L280-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L280-L281

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

theorem GroundTheory.Global.IdeleGroup.isOpen_standardOpenSubgroup : IsOpen (standardOpenSubgroup K : Set (IdeleGroup K)) := by sorry
