-- Prove2me | Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- name    : GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:12.106653+00:00
-- url     : https://prove2.me/theorems/581c3b54-9d70-4f4a-bc75-e7bb0674314a
-- title:
--   Restricted Product: continuous Units Equiv apply
-- statement:
--   The Restricted Product construction uses the continuous Units Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L68-L71

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
open GroundTheory.Global.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : Π i, S i}

theorem GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply (hBopen : ∀ i, IsOpen (B i : Set (R i)))
    (x : (Πʳ i, [R i, B i])ˣ) (i : ι) :
    ((continuousUnitsEquiv hBopen x i : (R i)ˣ) : R i) = (x : Πʳ i, [R i, B i]) i := by sorry

attribute [defeq] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
