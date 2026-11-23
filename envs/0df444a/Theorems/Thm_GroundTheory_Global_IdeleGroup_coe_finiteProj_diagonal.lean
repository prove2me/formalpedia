-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
-- name    : GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:47.790794+00:00
-- url     : https://prove2.me/theorems/04922158-20c5-4085-89ea-f83f32df50ff
-- title:
--   Idele Group: coe finite Proj diagonal
-- statement:
--   The Idele Group construction uses the coe finite Proj diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L181-L184

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

theorem GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
