-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/cbc097fd-f313-5ba9-a990-b74c3b45bf06
-- title:
--   Descent of a relative group law to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra, let $X$ be a scheme and $f \colon X \to \operatorname{Spec} A_0$ a morphism that is quasi-compact, quasi-separated and locally of finite presentation. Let $L$ be a relative group law over $A$ on the second projection $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A \to \operatorname{Spec} A$ (that is, for every scheme $T'$ and every $t \colon T' \to \operatorname{Spec} A$ a multiplication, unit and inversion on the set of morphisms from $T'$ to the base change whose composite with the structure morphism is $t$, satisfying associativity, both unit laws, left inversion, and naturality under precomposition with any $\psi \colon T'' \to T'$ over $\operatorname{Spec} A$), and let $s$ be a finite subset of $A$. Then there exist a finitely generated $A_0$-subalgebra $T \subseteq A$ with $s \subseteq T$, a relative group law $L_T$ over $T$ on $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} T \to \operatorname{Spec} T$, and a morphism $$c \colon X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A \to (X \times_{\operatorname{Spec} A_0} \operatorname{Spec} T) \times_{\operatorname{Spec} T} \operatorname{Spec} A$$ such that $c$ is an isomorphism, $c$ followed by the projection to $\operatorname{Spec} A$ is the structure morphism to $\operatorname{Spec} A$, $c$ followed by the two first projections is the projection to $X$, and $c$ is a homomorphism from $L$ to the base change of $L_T$ along $\operatorname{Spec}$ of $T \to A$: for every scheme $T'$, every $t \colon T' \to \operatorname{Spec} A$ and all points $x, y$ over $t$, the underlying morphism of $L$-product of $x$ and $y$ followed by $c$ equals the underlying morphism of the product of $x$ followed by $c$ and $y$ followed by $c$ in the base-changed law. Moreover, if $L$ is commutative then so is $L_T$.
--
--   This is the group-law component of the Grothendieck approximation results of EGA IV §8 (Théorème 8.8.2): a group law over an arbitrary $A_0$-algebra $A$ already comes, up to isomorphism over $A$, from one over some finitely generated $A_0$-subalgebra containing any prescribed finite set of elements. It feeds the descent of an abelian scheme together with its group law to a finitely generated subalgebra, and through that the limit arguments used for good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (L : RelativeGroupLaw A (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (Lₜ : RelativeGroupLaw ↥T (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))))
        (c : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
          pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
            (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
        (_ : IsIso c)
        (hc : c ≫ pullback.snd _ _ = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
        (_ : c ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))),
        (∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
            (x y : SchemeHomOver t (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
          (L.mul t x y).1 ≫ c =
            ((Lₜ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))).mul t
              ⟨x.1 ≫ c, by rw [Category.assoc, hc, x.2]⟩ ⟨y.1 ≫ c, by rw [Category.assoc, hc, y.2]⟩).1) ∧
        (L.IsCommutative → Lₜ.IsCommutative) := by sorry
