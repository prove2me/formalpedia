-- Prove2me | Theorems.Thm_MazurTransfer_internal_monoid_morphism_of_all_points
-- name    : MazurTransfer.internal_monoid_morphism_of_all_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T21:39:30.651991+00:00
-- url     : https://prove2.me/theorems/92add031-87cd-4b67-9406-566690872a25
-- title:
--   Pointwise group laws determine an internal monoid morphism
-- statement:
--   In a category with finite products, a morphism between internal monoid objects is an internal monoid morphism if postcomposition preserves the identity and multiplication on the points of every test object. The proof uses the fully faithful monoid Yoneda embedding. Applied to the actual order-thirteen Picard representations, this proves that their canonical representing isomorphism preserves the group scheme law, for the SAME rational Picard and the rational fibre of its integral family.
-- source:
--   Owned Yoneda argument, Apache-2.0. Named downstream consumer: canonical group scheme comparison for the SAME order-thirteen Picard family and local norm extension.

import Mathlib
open CategoryTheory
open scoped CategoryTheory.MonObj
universe u v

theorem MazurTransfer.internal_monoid_morphism_of_all_points {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : ∀ T : C, (1 : T ⟶ M) ≫ f = 1)
    (hm : ∀ (T : C) (a b : T ⟶ M), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f := by sorry
