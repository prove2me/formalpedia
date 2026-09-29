-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_comp_eq_of_exists_mul_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9660ef57-2e43-562c-ba64-941b53410bbc
-- title:
--   Normalising a lift of a relative group law at the unit section
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal. Let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$, i.e. a multiplication, unit and inverse on the sets $\{\varphi \colon T\text{-scheme point } t \to A_0\}$ of morphisms over each $t \colon T_1 \to \operatorname{Spec} T$, satisfying associativity, the two unit laws, left inverse, and naturality in $t$. Let $f \colon A \to \operatorname{Spec} T'$ be smooth, let $g \colon A_0 \to A$ make the square with $f_0$, $f$ and $\operatorname{Spec}(\pi)$ cartesian, and let $e$ be a section of $f$ (a morphism $\operatorname{Spec} T' \to A$ with $e \circ$ nothing after $f$ equal to the identity, i.e. $e$ followed by $f$ is $\mathrm{id}$) whose restriction, $\operatorname{Spec}(\pi)$ followed by $e$, equals the unit section of $L_0$ followed by $g$. Assume some $m' \colon A \times_{\operatorname{Spec} T'} A \to A$ satisfies $m'$ followed by $f$ equals $\mathrm{pr}_1$ followed by $f$, and that $g \times g$ followed by $m'$ equals the $L_0$-multiplication of the two projections $A_0 \times_{\operatorname{Spec} T} A_0 \to A_0$ followed by $g$. Then there is $m \colon A \times_{\operatorname{Spec} T'} A \to A$ with the same two properties which is in addition normalised at the section: $(e,e)$ followed by $m$ equals $e$.
--
--   This is the normalisation step in lifting the group law of an abelian scheme along a thickening with nilpotent kernel: an arbitrary lift of the multiplication is corrected so that the given lift of the unit section is a unit for it on the diagonal pair $(e,e)$. It is used by the constructions of lifts of the group law along small extensions and along extensions whose kernel is annihilated by the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_comp_eq_of_exists_mul_lift
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)
    (m' : pullback f f ⟶ A) (hm'f : m' ≫ f = pullback.fst f f ≫ f)
    (hm'μ : pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m' =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      pullback.lift e.1 e.1 rfl ≫ m = e.1 ∧
      pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by sorry
