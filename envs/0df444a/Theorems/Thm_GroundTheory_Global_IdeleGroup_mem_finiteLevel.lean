-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
-- name    : GroundTheory.Global.IdeleGroup.mem_finiteLevel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:10.835034+00:00
-- url     : https://prove2.me/theorems/01096cf7-18e5-4a07-8094-5a0e72a131fd
-- title:
--   Idele Group: mem finite Level
-- statement:
--   The Idele Group construction uses the mem finite Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L54-L56

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by sorry
