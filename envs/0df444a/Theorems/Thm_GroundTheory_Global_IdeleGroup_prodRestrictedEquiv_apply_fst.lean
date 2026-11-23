-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
-- name    : GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:57.990739+00:00
-- url     : https://prove2.me/theorems/dfdb7f93-3415-4e0a-9386-51fda3ce25e7
-- title:
--   Idele Group: prod Restricted Equiv apply fst
-- statement:
--   The Idele Group construction uses the prod Restricted Equiv apply fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L108-L110

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

theorem GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst (x : IdeleGroup K) :
    ((prodRestrictedEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
