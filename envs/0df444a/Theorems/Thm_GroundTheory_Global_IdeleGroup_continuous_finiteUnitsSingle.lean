-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteUnitsSingle
-- name    : GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:24.769232+00:00
-- url     : https://prove2.me/theorems/8c393d10-7d3a-4ba7-a6de-11cd39e39eef
-- title:
--   Idele Group: continuous finite Units Single
-- statement:
--   The Idele Group construction uses the continuous finite Units Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L36-L38

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

theorem GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteUnitsSingle (K := K) v) := by sorry
