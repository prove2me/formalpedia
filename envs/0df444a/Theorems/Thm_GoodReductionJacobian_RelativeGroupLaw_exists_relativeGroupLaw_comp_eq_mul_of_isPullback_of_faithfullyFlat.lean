-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0765bbc9-7ee2-5e14-bbe8-e4d8259b2c23
-- title:
--   Faithfully flat descent of a relative group law
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module, and write $S'' = S'\otimes_S S'$. Let $X, A', A''$ be schemes, and let $f : X \to \operatorname{Spec} S$, $f' : A' \to \operatorname{Spec} S'$ and $f'' : A'' \to \operatorname{Spec} S''$ be morphisms. Suppose $c : A' \to X$ makes the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ a pullback, and that $a_1, a_2 : A'' \to A'$ make the analogous squares over $\operatorname{Spec}$ of the two inclusions $S' \to S'\otimes_S S'$ (left and right) pullbacks, with $a_1$ followed by $c$ equal to $a_2$ followed by $c$. Let $L'$ be a relative group law for $f'$ over $S'$ and $L''$ one for $f''$ over $S''$; here a relative group law on a morphism $g : A \to \operatorname{Spec} R$ consists of multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } g = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, satisfying associativity, both unit laws, left inverse, and naturality under precomposition with $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume $a_1$ and $a_2$ are multiplicative on points: for every scheme $T$, every $t'' : T \to \operatorname{Spec} S''$ and all points $x, y$ of $A''$ over $t''$, the $L''$-product of $x$ and $y$ followed by $a_i$ equals the $L'$-product of $x$ followed by $a_i$ and $y$ followed by $a_i$, taken over $t''$ followed by $\operatorname{Spec}$ of the corresponding inclusion ($i = 1, 2$). Then there exists a relative group law $L$ for $f$ over $S$ such that $c$ is multiplicative on points, i.e. for every $T$, every $t' : T \to \operatorname{Spec} S'$ and all points $x, y$ of $A'$ over $t'$, the $L'$-product of $x$ and $y$ followed by $c$ equals the $L$-product of $x$ followed by $c$ and $y$ followed by $c$, taken over $t'$ followed by $\operatorname{Spec}$ of $S \to S'$; and such that $L$ is commutative whenever $L'$ is. Nothing is asserted about compatibility of $c$ with the units or inversions, nor about uniqueness of $L$.
--
--   This is the effectivity of a descent datum for a group law along a faithfully flat base change $S \to S'$, in the functor-of-points formulation: the scheme $X$ is given in advance, and only its group structure is descended from $A' = X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$, the cocycle condition being encoded by the group law $L''$ over $S' \otimes_S S'$ together with multiplicativity of the two cofaces $a_1, a_2$. It is used in the descent of polarised abelian schemes and in the companion statement identifying the descended unit section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' A'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hca : a₁ ≫ c = a₂ ≫ c)
    (L' : RelativeGroupLaw S' f') (L'' : RelativeGroupLaw (S' ⊗[S] S') f'')
    (ha₁mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₁ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1)
    (ha₂mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₂ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1) :
    ∃ L : RelativeGroupLaw S f,
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ c =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (L'.IsCommutative → L.IsCommutative) := by sorry
