-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/d307cf07-0841-5953-9d0c-2aeacf6c686d
-- title:
--   Symmetric invertible sheaf trivial modulo a square-zero ideal
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} R$, and let $L$ be a relative group law on $f$ over $R$ (a functorial group structure on $T$-points of $A$ over $\operatorname{Spec} R$, natural in $T$). Assume `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $R_1$ be a local noetherian $R$-algebra, $R_0$ a nontrivial $R$-algebra, and $\varphi : R_1 \to R_0$ a surjective $R$-algebra map whose kernel $I$ satisfies $x m = 0$ for all $x \in I$ and all $m$ in the maximal ideal of $R_1$; assume $2$ is a unit in $R_1$. Write $A_i$ for the pullback of $f$ along $\operatorname{Spec}$ of $R \to R_i$. Let $t : A_0 \to A_1$ be a morphism compatible with both projections: $t$ followed by the projection to $A$ is the projection $A_0 \to A$, and $t$ followed by $A_1 \to \operatorname{Spec} R_1$ is $A_0 \to \operatorname{Spec} R_0$ followed by $\operatorname{Spec} \varphi$. Let $L_1$ be a relative group law on $A_1 \to \operatorname{Spec} R_1$ over $R_1$ compatible with $L$: for every scheme $T$, every $t' : T \to \operatorname{Spec} R_1$ and all $T$-points $P, Q$ of $A_1$ over $t'$, the product $L_1.\mathrm{mul}\,t'\,P\,Q$ followed by $A_1 \to A$ equals the $L$-product of the images of $P$ and $Q$ in $A$ over $t'$ followed by $\operatorname{Spec}$ of $R \to R_1$. Finally let $M$ be a sheaf of modules on $A_1$ that is invertible (every point has an open neighbourhood over which $M$ pulls back to the unit), suppose the pullback of $M$ along $t$ is isomorphic to the monoidal unit, and suppose $M$ is symmetric in the sense that for every point $s$ of $\operatorname{Spec} R_1$ there is an open $U \ni s$ such that the pullbacks to the preimage of $U$ of the inverse-image of $M$ under the inversion morphism of $L_1$ and of $M$ itself are isomorphic. The conclusion is that $M$ is isomorphic to the monoidal unit on $A_1$, i.e. $M \cong \mathcal O_{A_1}$.
--
--   This is the uniqueness (injectivity) half of the deformation theory of line bundles on an abelian scheme along a small, square-zero thickening of the base: the kernel of $\operatorname{Pic}(A_1) \to \operatorname{Pic}(A_0)$ contains no nontrivial symmetric class once $2$ is invertible, the inversion automorphism acting by $-1$ on the relevant first cohomology. It is used for the corresponding statement over an Artinian local base and in the construction of symmetric line bundles on fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R₀] [Nontrivial R₀] [Algebra R R₁] [Algebra R R₀]
    (φ : R₁ →ₐ[R] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)
    (h2 : IsUnit (2 : R₁))

    (t : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
    (ht₁ : t ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))))
    (ht₂ : t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) =
          (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback t).obj M ≅ 𝟙_ _))
    (hsym : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁ M) :
    Nonempty (M ≅ 𝟙_ _) := by sorry
