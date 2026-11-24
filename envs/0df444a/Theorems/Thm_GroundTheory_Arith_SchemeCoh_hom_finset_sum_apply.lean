-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hom_finset_sum_apply
-- name    : GroundTheory.Arith.SchemeCoh.hom_finset_sum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:55.625514+00:00
-- url     : https://prove2.me/theorems/cff0d346-5f75-4a87-a261-52509109cee6
-- title:
--   Scheme Coh: hom finset sum apply
-- statement:
--   The Scheme Coh construction uses the hom finset sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L56-L62

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.hom_finset_sum_apply {M N : AddCommGrpCat.{v}} {α : Type*} (s : Finset α)
    (f : α → (M ⟶ N)) (x : M) : (∑ a ∈ s, f a).hom x = ∑ a ∈ s, (f a).hom x := by sorry
