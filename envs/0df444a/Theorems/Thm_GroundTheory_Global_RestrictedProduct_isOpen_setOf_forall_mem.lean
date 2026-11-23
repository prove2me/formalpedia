-- Prove2me | Theorems.Thm_GroundTheory_Global_RestrictedProduct_isOpen_setOf_forall_mem
-- name    : GroundTheory.Global.RestrictedProduct.isOpen_setOf_forall_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:48.264836+00:00
-- url     : https://prove2.me/theorems/bdeb4871-2ba9-4a4c-83f9-673d1ec7f469
-- title:
--   Restricted Product: is Open set Of forall mem
-- statement:
--   The Restricted Product construction uses the is Open set Of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L15-L35

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
open GroundTheory GroundTheory.Global
open GroundTheory.Global.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}

theorem GroundTheory.Global.RestrictedProduct.isOpen_setOf_forall_mem (hAopen : ∀ i, IsOpen (A i)) {V : ∀ i, Set (R i)}
    (hV : ∀ i, IsOpen (V i)) (hVA : ∀ᶠ i in cofinite, V i = A i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} := by sorry
