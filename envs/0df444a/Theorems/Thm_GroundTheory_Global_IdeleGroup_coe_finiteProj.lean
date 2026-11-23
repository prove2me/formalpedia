-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
-- name    : GroundTheory.Global.IdeleGroup.coe_finiteProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:33.078775+00:00
-- url     : https://prove2.me/theorems/164ae541-b1ac-4bd6-842f-07343a6b7365
-- title:
--   Idele Group: coe finite Proj
-- statement:
--   The Idele Group construction uses the coe finite Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L157-L159

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
variable {K}

theorem GroundTheory.Global.IdeleGroup.coe_finiteProj (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : 𝔸[K]).2 v := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_finiteProj
