-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_surjective
-- name    : GroundTheory.Global.IdeleClassGroup.ideleModule_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:41.44812+00:00
-- url     : https://prove2.me/theorems/de0994ab-63e6-5dee-aff3-a88a0d421a37
-- title:
--   Idele Class Group: idele Module surjective
-- statement:
--   The Idele Class Group construction uses the idele Module surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L237-L239

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
open GroundTheory.Global.IdeleClassGroup

theorem GroundTheory.Global.IdeleClassGroup.ideleModule_surjective : Function.Surjective (ideleModule K) := by sorry
