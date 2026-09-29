-- Prove2me | Theorems.Thm_HopfAlgebra_exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom
-- name    : HopfAlgebra.exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b368e7a6-ec81-5cac-9442-33e7a78957df
-- title:
--   Bialgebra maps induce morphisms of fppf point sheaves
-- statement:
--   Work on the small fppf site of $\operatorname{Spec}\mathbf Z$: its objects are the $\operatorname{Spec}\mathbf Z$-schemes whose structure morphism is flat and locally of finite presentation, equipped with the associated small Grothendieck topology. Let $F,F'$ be sheaves of abelian groups on this site, let $H,H'$ be commutative rings carrying Hopf algebra structures over $\mathbf Z$, and suppose given, for every object $U$ of the site, additive isomorphisms $e_U\colon F(U)\xrightarrow{\ \sim\ }\operatorname{Hom}_{\mathbf Z\text{-alg}}(H,\Gamma(U,\top))$ and $e'_U\colon F'(U)\xrightarrow{\ \sim\ }\operatorname{Hom}_{\mathbf Z\text{-alg}}(H',\Gamma(U,\top))$, where the algebra maps into the global sections of the scheme underlying $U$ are given the convolution product coming from the Hopf structure, written additively. These identifications are assumed natural in the following pointwise sense: for every morphism $f\colon U\to V$ in the site, every section $s$ over $V$ and every $h$, the algebra map attached to the restriction of $s$ sends $h$ to the image under $\Gamma(f)$ of the value at $h$ of the algebra map attached to $s$; likewise for $F'$ and $H'$. Finally let $\pi\colon H'\to H$ be a homomorphism of $\mathbf Z$-bialgebras. The conclusion asserts the existence of a morphism of sheaves $\iota\colon F\to F'$ such that for every object $U$, every $s\in F(U)$ and every $h'\in H'$, the algebra map attached to $\iota_U(s)$ sends $h'$ to the value at $\pi(h')$ of the algebra map attached to $s$; that is, $\iota$ acts on points by precomposition with $\pi$.
--
--   This is the functor-of-points translation of the fact that a homomorphism of bialgebras $H'\to H$ over $\mathbf Z$ corresponds to a homomorphism of affine group schemes $\operatorname{Spec} H\to\operatorname{Spec} H'$, here realised as a morphism of the associated sheaves of points on the small fppf site of $\operatorname{Spec}\mathbf Z$. It is used to produce the transition maps between the torsion sheaves occurring in the analysis of the Néron model of the Jacobian, in [`ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding) and [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem HopfAlgebra.exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom
    (F F' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (H H' : Type) [CommRing H] [CommRing H'] [HopfAlgebra ℤ H] [HopfAlgebra ℤ H']
    (eF : ∀ U : specInt.Fppf, F.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (heF : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : F.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (eF U (F.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (eF V s)) h))
    (eF' : ∀ U : specInt.Fppf, F'.1.obj (Opposite.op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (heF' : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : F'.1.obj (Opposite.op V)) (h : H'),
        (Additive.toMul (eF' U (F'.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (eF' V s)) h))
    (π : H' →ₐc[ℤ] H) :
    ∃ incl : F ⟶ F', ∀ (U : specInt.Fppf) (s : F.1.obj (Opposite.op U)) (h' : H'),
      (Additive.toMul (eF' U (incl.1.app (Opposite.op U) s))) h' = (Additive.toMul (eF U s)) (π h') := by sorry
