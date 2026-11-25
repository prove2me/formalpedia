-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isEmbedding_val_inv
-- name    : GroundTheory.Global.IdeleGroup.isEmbedding_val_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:01.849072+00:00
-- url     : https://prove2.me/theorems/072337be-57c8-47a4-baab-c1f5d642434c
-- title:
--   Idele Group: is Embedding val inv
-- statement:
--   The Idele Group construction uses the is Embedding val inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L16-L19

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

theorem GroundTheory.Global.IdeleGroup.isEmbedding_val_inv :
    IsEmbedding (fun x : IdeleGroup K ↦ ((x : 𝔸[K]), ((x⁻¹ : IdeleGroup K) : 𝔸[K]))) := by sorry
