-- Prove2me | Theorems.Thm_GroundTheory_Global_RestrictedProduct_isTopologicalBasis
-- name    : GroundTheory.Global.RestrictedProduct.isTopologicalBasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:14.141581+00:00
-- url     : https://prove2.me/theorems/04451306-bd80-426d-a7d1-14336b14af70
-- title:
--   Restricted Product: is Topological Basis
-- statement:
--   The Restricted Product construction uses the is Topological Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L37-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L37-L90

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

theorem GroundTheory.Global.RestrictedProduct.isTopologicalBasis (hAopen : ∀ i, IsOpen (A i)) :
    IsTopologicalBasis {s : Set (Πʳ i, [R i, A i]) | ∃ V : ∀ i, Set (R i),
      (∀ i, IsOpen (V i)) ∧ (∀ᶠ i in cofinite, V i = A i) ∧ s = {x | ∀ i, x i ∈ V i}} := by sorry
