-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsSingle_mem_finiteLevel
-- name    : GroundTheory.Global.IdeleGroup.finiteUnitsSingle_mem_finiteLevel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:32.098815+00:00
-- url     : https://prove2.me/theorems/a24344f2-4c12-4227-9ad2-dd21f515edd2
-- title:
--   Idele Group: finite Units Single mem finite Level
-- statement:
--   The Idele Group construction uses the finite Units Single mem finite Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L66-L74

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

theorem GroundTheory.Global.IdeleGroup.finiteUnitsSingle_mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ}
    {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} (hx : x ∈ unitsLevel v (n v)) :
    finiteUnitsSingle v x ∈ finiteLevel n := by sorry
