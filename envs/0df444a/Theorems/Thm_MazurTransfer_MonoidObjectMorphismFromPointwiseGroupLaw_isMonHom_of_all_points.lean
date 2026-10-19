-- Prove2me | Theorems.Thm_MazurTransfer_MonoidObjectMorphismFromPointwiseGroupLaw_isMonHom_of_all_points
-- name    : MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T08:23:14.773203+00:00
-- url     : https://prove2.me/theorems/3e20b1f4-98e8-4352-b6c2-c46ec37ac321
-- title:
--   A morphism preserving all pointwise monoid laws is an internal monoid morphism
-- statement:
--   Let $\mathcal C$ be a Cartesian monoidal category, let $M,N$ be monoid objects, and let $f:M\to N$ be a morphism. Suppose that for every object $T$ and every pair of generalized points $a,b:T\to M$, postcomposition with $f$ preserves the unit and multiplication: $$f\circ1_T=1_T,\qquad f\circ(ab)=(f\circ a)(f\circ b).$$ Then $f$ is an internal monoid morphism. This turns the pointwise multiplication identities for Picard representations and norm maps into morphisms of internal group objects.
-- source:
--   Original complete isMonHom_of_all_points contract and proof body from MazurTheorem MonoidObjectMorphismFromPointwiseGroupLaw.lean, Apache-2.0, Vas and contributors. Uses the fully faithful monoid-valued Yoneda embedding from the pinned Mathlib environment. The original statement, both universe parameters and full proof body are retained; section variables are made explicit for the platform solution. The complete original closed type is kernel-compared with both the checked solution and public statement. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: PicardCanonicalRepresentationGroupIsomorphism, the actual Picard diamond and nineteen-norm endomorphisms as internal group morphisms.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a morphism preserving identity and multiplication on all
test objects is an internal monoid morphism, by the fully faithful monoid
Yoneda embedding. Named downstream consumer: the actual Picard diamond
and nineteen-norm endomorphisms as internal group morphisms.
-/
import Mathlib
noncomputable section
universe u v
open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

theorem MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : ∀ T : C, (1 : T ⟶ M) ≫ f = 1)
    (hm : ∀ (T : C) (a b : T ⟶ M), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) :
    IsMonHom f := by sorry
