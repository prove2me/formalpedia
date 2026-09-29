-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- name    : GoodReductionJacobian.exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/2191b016-2075-544c-a2e0-43e769245d6e
-- title:
--   Algebraisation of a compatible tower of group laws
-- statement:
--   Let $R$ be a noetherian commutative ring that is $I$-adically complete for an ideal $I$, let $A$ be a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and suppose $f$ is projective in the explicit sense that there is a closed immersion $\iota : A \to \operatorname{Proj}$ of the homogeneous coordinate ring $R[x_0,\dots,x_N]$ with $\iota$ followed by the structure map $\operatorname{ProjSpace.}\pi$ equal to $f$. For each $n$ put $A_n := A \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$, with projections $\mathrm{adicThickening}\iota$ to $A$ and $\mathrm{adicThickeningToBase}$ to $\operatorname{Spec}(R/I^{n+1})$, and transition morphisms $A_n \to A_{n+1}$. Assume given, for every $n$, a relative group law $L_n$ on $A_n \to \operatorname{Spec}(R/I^{n+1})$, i.e. a functorial group structure on the sets of $T$-points over each $t : T \to \operatorname{Spec}(R/I^{n+1})$, and assume the tower is compatible: for all $n$, all $t : T \to \operatorname{Spec}(R/I^{n+1})$ and all points $P, Q$ of $A_n$ over $t$, the product $L_n(P,Q)$ followed by the transition $A_n \to A_{n+1}$ equals the $L_{n+1}$-product of $P$ and $Q$ pushed along the transition, taken over $t$ composed with $\operatorname{Spec}$ of the projection $R/I^{n+2} \to R/I^{n+1}$. Then there exists a morphism $m : A \times_{\operatorname{Spec} R} A \to A$ with $m$ followed by $f$ equal to the first projection followed by $f$, such that for every $n$, every $t : T \to \operatorname{Spec}(R/I^{n+1})$ and all points $x, y$ of $A_n$ over $t$, the morphism $T \to A \times_{\operatorname{Spec} R} A$ determined by $x$ and $y$ (composed into $A$) followed by $m$ equals $L_n(x,y)$ followed by $A_n \to A$.
--
--   This is the formal algebraisation step for the multiplication: a compatible tower of group laws on the $I$-adic thickenings of a projective $R$-scheme with $R$ noetherian and $I$-adically complete is glued into a single multiplication morphism $A \times_R A \to A$ over $R$. It is proved by exhibiting $A \times_R A$ as projective over $R$ via the Segre-type statement [`AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion`](thm.html#AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion) and applying the formal existence theorem [`AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj), and it feeds the construction of the identity section and the full relative group law on $A$ in the good-reduction theory of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits GoodReductionJacobian NeronModelInfra
open AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
          ⟨P.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n := by sorry
