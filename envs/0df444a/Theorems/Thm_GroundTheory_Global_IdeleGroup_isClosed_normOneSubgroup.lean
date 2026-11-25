-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isClosed_normOneSubgroup
-- name    : GroundTheory.Global.IdeleGroup.isClosed_normOneSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:26.600898+00:00
-- url     : https://prove2.me/theorems/905749e1-0c59-4eed-a6c7-ea9ea6b34e8b
-- title:
--   Idele Group: is Closed norm One Subgroup
-- statement:
--   The Idele Group construction uses the is Closed norm One Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L208-L214

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
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
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
variable (K)

theorem GroundTheory.Global.IdeleGroup.isClosed_normOneSubgroup : IsClosed (normOneSubgroup K : Set (IdeleGroup K)) := by sorry
