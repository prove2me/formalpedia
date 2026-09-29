-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/9211a4d1-dad7-54c5-a87b-78d3a0702e5f
-- title:
--   Lifting a commutative group law along a small surjection
-- statement:
--   Let $T'$ be an Artinian local commutative ring with maximal ideal $\mathfrak m$ whose residue field is algebraically closed, let $T$ be a commutative ring, and let $\pi \colon T' \to T$ be a surjective ring homomorphism whose kernel is a nilpotent ideal and satisfies $\ker \pi \cdot \mathfrak m = 0$. Let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$ — that is, for every scheme $S$ and every $t \colon S \to \operatorname{Spec} T$, a multiplication, unit and inverse on the set of morphisms $S \to A_0$ over $t$, associative, unital, with left inverses, and natural with respect to precomposition along morphisms of $T$-schemes — assumed commutative, and suppose $f_0$ satisfies `AbelianSchemePropertyBundle`: it is smooth, proper, its fibres over points of $\operatorname{Spec} T$ are connected, and it carries some relative group law. Let $f \colon A \to \operatorname{Spec} T'$ be smooth and proper and let $g \colon A_0 \to A$ exhibit the square formed by $g$, $f_0$, $f$ and $\operatorname{Spec} \pi$ as a pullback. Then there is a relative group law $L$ on $f$ over $T'$ which is commutative and for which $f$ again satisfies `AbelianSchemePropertyBundle`, such that for every scheme $S$, every $t \colon S \to \operatorname{Spec} T$ and all $P, Q \colon S \to A_0$ over $t$, the composite $g \circ L_0.\mathrm{mul}(t)(P,Q)$ equals the $L$-product, over the base point $\operatorname{Spec} \pi \circ t$, of $g \circ P$ and $g \circ Q$.
--
--   This is the deformation-theoretic statement that a smooth proper lift of an abelian scheme along a small surjection of Artinian local rings is again an abelian scheme, with a group law extending the given one compatibly with the closed fibre, as in Mumford's Geometric Invariant Theory, Ch. 6 §3. It feeds the step-by-step lifting of abelian schemes (and of Jacobians with good reduction) along a chain of small surjections, being used in the construction of pullback data for `AbelianSchemePropertyBundle` and in the production of relative group laws on smooth lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_ker_mul_maximalIdeal_eq_bot
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    ∃ (L : RelativeGroupLaw T' f) (_ : L.IsCommutative) (_ : AbelianSchemePropertyBundle T' f),
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t f₀),
        (L₀.mul t P Q).1 ≫ g =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 := by sorry
