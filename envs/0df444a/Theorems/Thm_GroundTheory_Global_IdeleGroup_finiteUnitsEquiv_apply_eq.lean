-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply_eq
-- name    : GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:41.446992+00:00
-- url     : https://prove2.me/theorems/8d6ad1fe-bfb9-4375-b59e-cda93be218a6
-- title:
--   Idele Group: finite Units Equiv apply eq
-- statement:
--   The Idele Group construction uses the finite Units Equiv apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L76-L78

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

theorem GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x := by sorry
