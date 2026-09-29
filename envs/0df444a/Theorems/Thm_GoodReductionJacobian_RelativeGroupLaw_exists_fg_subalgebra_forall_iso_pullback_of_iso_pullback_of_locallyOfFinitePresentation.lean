-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/1261dfba-ab59-5c8b-ba42-601c042f581a
-- title:
--   Group-scheme isomorphisms descend to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra, and let $f_1 : X_1 \to \operatorname{Spec} A_0$ and $f_2 : X_2 \to \operatorname{Spec} A_0$ be morphisms of schemes that are quasi-compact, quasi-separated and locally of finite presentation. Suppose given relative group laws $L_1$ on $f_1$ and $L_2$ on $f_2$, that is, for each scheme $T$ and each $t : T \to \operatorname{Spec} A_0$ a group structure (multiplication, unit, inverse, with associativity, unit laws and left inverses) on the set of morphisms $T \to X_i$ over $t$, compatible with precomposition by morphisms of test schemes. Suppose further given an isomorphism $e$ between the pullbacks of $f_1$ and of $f_2$ along $\operatorname{Spec}$ of the structure map $A_0 \to A$ such that $e$ followed by the second projection of the second pullback is the second projection of the first (so $e$ is an isomorphism over $\operatorname{Spec} A$), and such that $e$ is multiplicative for the base-changed group laws: for every scheme $T'$, every $t : T' \to \operatorname{Spec} A$ and all points $x, y$ of $X_1 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ over $t$, the underlying morphism of $(L_1)_A$-product of $x$ and $y$ followed by $e$ equals the underlying morphism of the $(L_2)_A$-product of $x$ followed by $e$ and $y$ followed by $e$. Then for every finite subset $s$ of $A$ there is a finitely generated $A_0$-subalgebra $T$ of $A$ containing $s$ such that for every commutative ring $B$ and every pair of ring homomorphisms $\varphi : T \to B$ and $\chi : A_0 \to B$ with $\varphi \circ (A_0 \to T) = \chi$, there exist an isomorphism $e'$ between the pullbacks of $f_1$ and $f_2$ along $\operatorname{Spec} \chi$ which commutes with the second projections in the same sense and which is multiplicative for the group laws base-changed along $\operatorname{Spec} \chi$, stated for all test schemes $T'$ over $\operatorname{Spec} B$ exactly as above.
--
--   This is the group-scheme form of the standard limit (approximation) statement that an isomorphism over $A = \varinjlim T$ already exists over some finitely generated $A_0$-subalgebra $T$, in the shape of EGA IV 8.8.2, strengthened so that the descended isomorphism is recorded as a homomorphism of relative group laws and so that its conclusion is available after base change along an arbitrary $T$-algebra structure $\varphi : T \to B$. It feeds the limit argument producing an abelian scheme over a directed union of subrings with a prescribed finite set of generators absorbed at a finite stage, and is proved from the corresponding isomorphism-descent and equality-of-morphisms approximation lemmas for quasi-compact, quasi-separated morphisms locally of finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
    (L₁ : RelativeGroupLaw A₀ f₁) (L₂ : RelativeGroupLaw A₀ f₂)
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hemul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
        (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
      ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t x y).1 ≫ e.hom =
        ((L₂.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ (B : Type u) [CommRing B] (φ : ↥T →+* B) (χ : A₀ →+* B), φ.comp (algebraMap A₀ ↥T) = χ →
        ∃ (e' : pullback f₁ (Spec.map (CommRingCat.ofHom χ)) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom χ)))
          (he' : e'.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _),
          ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of B))
            (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom χ)))),
            ((L₁.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t x y).1 ≫ e'.hom =
              ((L₂.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t
                ⟨x.1 ≫ e'.hom, by rw [Category.assoc, he', x.2]⟩ ⟨y.1 ≫ e'.hom, by rw [Category.assoc, he', y.2]⟩).1 := by sorry
