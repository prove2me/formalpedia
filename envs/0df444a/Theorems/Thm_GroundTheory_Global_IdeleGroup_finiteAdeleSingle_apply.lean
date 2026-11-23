-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply
-- name    : GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:41.830918+00:00
-- url     : https://prove2.me/theorems/b9125390-bc90-4618-98f2-ce224417e63c
-- title:
--   Idele Group: finite Adele Single apply
-- statement:
--   The Idele Group construction uses the finite Adele Single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L105-L107

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
open Classical

theorem GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply (v w : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x w = Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) ↦
      u.adicCompletion K) v x w := by sorry
