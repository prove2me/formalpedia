-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/748874d4-1369-57ff-9db8-d9c05e1c7408
-- title:
--   Coordinate Hopf algebra of an affine flat relative group law
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $g : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $g$ over $R$: for each scheme $T$ and each structure morphism $t : T \to \operatorname{Spec} R$, a multiplication, a unit and an inversion on the set $\{\varphi : T \to A \mid \varphi \text{ followed by } g = t\}$, satisfying associativity, both unit laws and left inverse, and natural in the sense that precomposition with any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$ carries the multiplication for $t$ to that for $t'$. Assume moreover that each of these multiplications is commutative, and that $g$ is an affine morphism, flat and locally of finite type. Give $\Gamma(A,\top)$ the $R$-algebra structure coming from the structure map (the inverse of $\Gamma\!\operatorname{Spec}$-iso followed by $g$ on global sections); $A$ is then affine. The assertion is that there exist a type $H$ of the same universe carrying a commutative ring and a Hopf $R$-algebra structure, such that $H$ is a finite-type $R$-algebra, flat as an $R$-module and cocommutative as a coalgebra, together with an $R$-algebra isomorphism $\mathrm{iso} : H \simeq \Gamma(A,\top)$ and, for every commutative $R$-algebra $T$, a bijection $e_T$ from the $R$-algebra homomorphisms $H \to T$, regarded with their convolution multiplication, to the morphisms $\operatorname{Spec} T \to A$ over $\operatorname{Spec} R$ (those $\varphi$ whose composite with $g$ is $\operatorname{Spec}$ of $\operatorname{algebraMap} R\,T$), subject to three compatibilities: the underlying morphism of $e_T(\varphi)$ is $\operatorname{Spec}$ of the ring map underlying $\varphi \circ \mathrm{iso}^{-1}$ followed by the inverse of $A.\mathrm{isoSpec}$; $e_T$ sends the convolution product $\varphi\psi$ to $L$-multiplication of $e_T(\varphi)$ and $e_T(\psi)$; and for every $R$-algebra map $\sigma : T \to T'$ the underlying morphism of $e_{T'}(\sigma \circ \varphi)$ is $\operatorname{Spec}\sigma$ followed by that of $e_T(\varphi)$.
--
--   This is the anti-equivalence between affine flat commutative group schemes over $R$ and commutative cocommutative flat Hopf $R$-algebras of finite type, in the form that realises the coordinate Hopf algebra concretely as the global sections of $A$ together with its functor of points. It is used in the treatment of torsion on affine relative group laws, of kernels of multiplication over henselian local rings, and in the Hopf-algebra description of the identity component of the Néron model attached to $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsAffineHom g] [Flat g] [LocallyOfFiniteType g] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Algebra.FiniteType R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (iso : H ≃ₐ[R] Γ(A, ⊤))
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          (e T φ).1 =
            Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (σ : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (σ.comp φ.ofConv))).1 =
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e T φ).1) := by sorry
