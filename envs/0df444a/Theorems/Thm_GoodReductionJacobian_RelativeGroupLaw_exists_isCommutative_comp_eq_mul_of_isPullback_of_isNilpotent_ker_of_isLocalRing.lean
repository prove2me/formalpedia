-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/bf502257-e225-5128-874a-b4b12beab14f
-- title:
--   Group law lifts along nilpotent thickenings of Artin local bases
-- statement:
--   Let $T'$ be a commutative local Artinian ring, $T$ a commutative ring, and $\pi : T' \to T$ a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $f_0 : A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$, i.e. a group structure on the sets $\{\varphi : S \to A_0 \mid \varphi \text{ followed by } f_0 = t\}$ of $S$-points over each $t : S \to \operatorname{Spec} T$, natural in the base $t$, and assume $L_0$ is commutative and that $f_0$ satisfies `AbelianSchemePropertyBundle`: $f_0$ is smooth and proper, each fibre of the underlying map of spaces is connected, and a relative group law exists. Let $f : A \to \operatorname{Spec} T'$ be smooth and proper and let $g : A_0 \to A$ make the square formed by $g$, $f_0$, $f$ and $\operatorname{Spec}(\pi)$ a pullback. Then there is a relative group law $L$ on $f$ over $T'$, commutative, with $f$ again satisfying `AbelianSchemePropertyBundle` over $T'$, such that for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all $S$-points $P, Q$ of $A_0$ over $t$, the morphism $L_0.\mathrm{mul}\,t\,P\,Q$ followed by $g$ equals the underlying morphism of $L.\mathrm{mul}$ at the base $t$ followed by $\operatorname{Spec}(\pi)$, applied to $P$ followed by $g$ and $Q$ followed by $g$.
--
--   This is the infinitesimal lifting step for group laws on abelian schemes: a commutative group law on an abelian scheme over an Artin local base propagates to any smooth proper lift across a surjection with nilpotent kernel, with $g$ a homomorphism on points. It is obtained from the corresponding statement for small extensions ($\ker \pi \cdot \mathfrak m_{T'} = 0$) and is used in the construction of relative group laws on Jacobians over adic thickenings and completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
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
