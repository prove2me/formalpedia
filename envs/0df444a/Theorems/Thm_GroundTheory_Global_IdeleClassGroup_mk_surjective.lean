-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
-- name    : GroundTheory.Global.IdeleClassGroup.mk_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:42.883615+00:00
-- url     : https://prove2.me/theorems/14dab5c8-fdc3-46f3-95cc-3ebb898f79eb
-- title:
--   Idele Class Group: mk surjective
-- statement:
--   The Idele Class Group construction uses the mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L79-L79

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

theorem GroundTheory.Global.IdeleClassGroup.mk_surjective : Function.Surjective (mk K) := by sorry
