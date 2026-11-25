-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:57.862828+00:00
-- url     : https://prove2.me/theorems/7644a2ff-40f9-451d-b4b7-9c8d58578a35
-- title:
--   Idele Group: mem standard Open Subgroup
-- statement:
--   The Idele Group construction uses the mem standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L273-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L273-L278

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

theorem GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by sorry
