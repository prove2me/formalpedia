-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/38c82bb4-a1eb-5597-a211-816f267fc4d4
-- title:
--   Hopf points of an affine group law over arbitrary test schemes
-- statement:
--   Let $X$ be a scheme and $g_X\colon X\to\operatorname{Spec}\mathbb Z$ a morphism which is an affine morphism, and let $L_X$ be a relative group law over $\mathbb Z$ on $g_X$: a family of group structures (a multiplication, unit and inverse satisfying associativity, unit and inverse laws) on each set $\{\varphi : T\to X \mid \varphi\,;\,g_X = t\}$ of $T$-points over $t\colon T\to\operatorname{Spec}\mathbb Z$, compatible with precomposition along any $\psi\colon T'\to T$ with $\psi\,;\,t=t'$. Let $H$ be a commutative ring carrying a Hopf $\mathbb Z$-algebra structure, and suppose given, for every commutative $\mathbb Z$-algebra $T$, a bijection $e_{\mathrm{Pts}}(T)$ from $\operatorname{Hom}_{\mathbb Z\text{-alg}}(H,T)$ with its convolution product to the set of morphisms $\operatorname{Spec}T\to X$ whose composite with $g_X$ is $\operatorname{Spec}$ of $\mathbb Z\to T$, such that $e_{\mathrm{Pts}}(T)$ carries the convolution product to $L_X$'s multiplication, and such that for every $\mathbb Z$-algebra map $\sigma\colon T\to T'$ the point attached to $\sigma\circ\varphi$ is $\operatorname{Spec}\sigma$ followed by the point attached to $\varphi$. The conclusion asserts the existence of a family of bijections $e_U$, one for every scheme $U$ and every $u\colon U\to\operatorname{Spec}\mathbb Z$, from the $U$-points of $g_X$ over $u$ to $\operatorname{Hom}_{\mathbb Z\text{-alg}}(H,\Gamma(U,\mathcal O_U))$ with its convolution product, such that: each point $y$ equals $U\to\operatorname{Spec}\Gamma(U,\mathcal O_U)$ followed by the point $e_{\mathrm{Pts}}(\Gamma(U,\mathcal O_U))(e_U(y))$; each $e_U$ takes $L_X$'s multiplication to the convolution product; and for $\psi\colon V\to U$ with $\psi\,;\,u=v$, $e_V$ of $\psi\,;\,y$ is $e_U(y)$ followed by the restriction map $\Gamma(U,\mathcal O_U)\to\Gamma(V,\mathcal O_V)$, evaluated elementwise on $H$.
--
--   This extends a functor-of-points description of an affine group scheme over $\mathbb Z$ by a Hopf algebra from affine test schemes to arbitrary test schemes, the group law being matched with convolution and base change with restriction of sections. It is used in the comparison of the points sheaf of $X$ with the Hopf points sheaf, and is cited by [`GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
    {X : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of ℤ)} (LX : RelativeGroupLaw ℤ gX) [IsAffineHom gX]
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LX.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1) :
    ∃ eU : ∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)), SchemeHomOver u gX ≃ WithConv (H →ₐ[ℤ] Γ(U, ⊤)),

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y : SchemeHomOver u gX),
        y.1 = U.toSpecΓ ≫ (ePts Γ(U, ⊤) (eU U u y)).1) ∧

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y y' : SchemeHomOver u gX),
        eU U u (LX.mul u y y') = eU U u y * eU U u y') ∧

      (∀ (U V : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (v : V ⟶ Spec (CommRingCat.of ℤ)) (ψ : V ⟶ U)
          (hψ : ψ ≫ u = v) (y : SchemeHomOver u gX) (h : H),
        (eU V v (GoodReductionJacobian.schemeHomOverComp ψ hψ y)).ofConv h = (Scheme.Γ.map ψ.op) ((eU U u y).ofConv h)) := by sorry
