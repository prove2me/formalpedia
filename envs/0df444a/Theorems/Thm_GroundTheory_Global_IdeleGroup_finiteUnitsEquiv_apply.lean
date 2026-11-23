-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
-- name    : GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:30.967255+00:00
-- url     : https://prove2.me/theorems/755376ce-fe5a-4a11-9b73-5673df3bb66d
-- title:
--   Idele Group: finite Units Equiv apply
-- statement:
--   The Idele Group construction uses the finite Units Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L92-L95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
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
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteUnitsEquiv K x v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
