-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
-- name    : GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:01.277869+00:00
-- url     : https://prove2.me/theorems/6895c65b-cfc1-4d20-8e4d-522d82014767
-- title:
--   Idele Group: finite Component finite Units Single
-- statement:
--   The Idele Group construction uses the finite Component finite Units Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L41-L44

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

theorem GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finiteComponent v (finiteUnitsSingle v x) = x := by sorry
