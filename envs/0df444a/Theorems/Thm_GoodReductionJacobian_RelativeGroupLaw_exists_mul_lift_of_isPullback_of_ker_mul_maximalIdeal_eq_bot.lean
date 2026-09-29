-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/92fc6701-a44d-5895-b54a-d25d0d6b89b6
-- title:
--   Lifting the multiplication across a small surjection
-- statement:
--   Let $T'$ be a commutative Artinian local ring of universe level $u$ whose residue field is algebraically closed, let $T$ be a commutative ring, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is nilpotent and satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$, so that $\pi$ is a small surjection. Let $f_0 : A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$, that is, functorial multiplication, unit and inverse operations on the sets of $T$-morphisms $t : X \to \operatorname{Spec} T$ lifting to $A_0$ (pairs $(\varphi, \varphi \circ f_0 = t)$), satisfying associativity, the unit laws, left inverses and compatibility with base change along any $\psi$ over $\operatorname{Spec} T$; assume $L_0$ is commutative and that $f_0$ satisfies `AbelianSchemePropertyBundle`, i.e. $f_0$ is smooth, proper, has connected fibres over every point, and admits some relative group law. Let $f : A \to \operatorname{Spec} T'$ be smooth and proper, and let $g : A_0 \to A$ exhibit $f_0$ as the base change of $f$ along $\operatorname{Spec}\pi$ (the square $g, f_0, f, \operatorname{Spec}\pi$ is a pullback). Let $e$ be a section of $f$, i.e. a morphism $\operatorname{Spec} T' \to A$ with $e$ followed by $f$ the identity, whose restriction along $\operatorname{Spec}\pi$ is the unit of $L_0$ followed by $g$. Then there is a morphism $m : A \times_{\operatorname{Spec} T'} A \to A$ such that $m$ followed by $f$ equals the first projection followed by $f$; the section $(e,e)$ of the fibre product followed by $m$ equals $e$; and $(g \circ \mathrm{pr}_1, g \circ \mathrm{pr}_2) : A_0 \times_{\operatorname{Spec} T} A_0 \to A \times_{\operatorname{Spec} T'} A$ followed by $m$ equals the $L_0$-product of the two projections of $A_0 \times_{\operatorname{Spec} T} A_0$ followed by $g$.
--
--   This is the existence of a lift of the multiplication of an abelian scheme to a smooth proper deformation across a small surjection, normalised so that the lifted multiplication sends the pair of unit sections to the unit section; it is the analogue of Mumford's criterion for lifting the group law of an abelian variety. It is used in the construction of a relative group law on the lift, being cited by the statement that produces a commutative relative group law over $T'$ extending $L_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      pullback.lift e.1 e.1 rfl ≫ m = e.1 ∧
      pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by sorry
