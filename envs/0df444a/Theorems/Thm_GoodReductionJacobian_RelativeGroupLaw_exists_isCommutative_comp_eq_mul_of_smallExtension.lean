-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_smallExtension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d5cf1a34-a48a-5d1e-8b78-92e58967bd4b
-- title:
--   Lifting a commutative group law along a small extension
-- statement:
--   Let $T'$ be a commutative local Artinian ring and $T$ a commutative ring, both in a fixed universe, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is nilpotent and satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$, so that $\pi$ is a small extension. Let $f_0 : A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$ over $T$ — that is, functorial multiplication, unit and inverse operations on the sets $\{\varphi : S \to A_0 \mid \varphi \text{ over } t\}$ of $S$-points over each $t : S \to \operatorname{Spec} T$, satisfying associativity, the unit laws, left inversion and compatibility with base change — which is commutative, and assume $f_0$ carries the bundle of abelian-scheme properties: $f_0$ is smooth and proper, each fibre $f_0^{-1}(s)$ over a point of $\operatorname{Spec} T$ is connected, and a relative group law exists. Let $f : A \to \operatorname{Spec} T'$ be smooth and proper and let $g : A_0 \to A$ exhibit $f_0$ as the base change of $f$ along $\operatorname{Spec}$ of $\pi$ (a pullback square). Then there exists a relative group law $L$ on $f$ over $T'$ which is commutative, $f$ satisfies the same bundle of abelian-scheme properties (smooth, proper, connected fibres, group law), and $g$ is a homomorphism in the strong functorial sense: for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all $P, Q : S \to A_0$ over $t$, the composite of $L_0$-product of $P$ and $Q$ with $g$ equals the $L$-product of $P$ followed by $g$ and $Q$ followed by $g$, taken over the base point $t$ followed by $\operatorname{Spec}$ of $\pi$.
--
--   This is the infinitesimal lifting step for abelian schemes over Artinian local rings, in the form used for Mumford's result that a smooth proper lift of an abelian scheme along a small surjection inherits a commutative group law compatible with the reduction map. It feeds the induction over a filtration of the kernel that yields the corresponding statement for an arbitrary surjection of local rings with nilpotent kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_smallExtension.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
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
