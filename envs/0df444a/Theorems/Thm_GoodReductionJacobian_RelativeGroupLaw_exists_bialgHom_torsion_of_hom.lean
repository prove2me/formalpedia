-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_torsion_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/61a476e0-9e58-5e9a-8df5-68cc4e2005e3
-- title:
--   Functoriality of torsion Hopf algebras under homomorphisms of group laws
-- statement:
--   Let $R$ be a commutative ring, and let $g : B \to \operatorname{Spec} R$ and $f : J \to \operatorname{Spec} R$ be morphisms of schemes carrying relative group laws $L_B$ and $L$ over $R$: that is, functorial multiplication, unit and inversion operations on the sets of sections $\{\varphi : T \to B \mid \varphi \circ g = t\}$, for morphisms $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inversion, and compatibility with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $u : B \to J$ satisfy $u$ followed by $f$ equal to $g$, and assume $u$ is a homomorphism: for all $t : T \to \operatorname{Spec} R$ and all sections $x, y$ of $g$ over $t$, post-composing $L_B.\mathrm{mul}\,t\,x\,y$ with $u$ gives $L.\mathrm{mul}\,t$ applied to the post-composites of $x$ and $y$. Let $n \in \mathbb{N}$, and let $H_B$, $H_J$ be commutative rings with Hopf $R$-algebra structures, equipped for each commutative $R$-algebra $T$ with bijections $e_B$, $e_J$ from the convolution monoids of $R$-algebra maps $H_B \to T$, respectively $H_J \to T$, onto the sets of $T$-points killed by $n$ (those $x$ with $\mathrm{nsmul}\,n\,x$ the unit) of $L_B$, respectively $L$, at the structure morphism $\operatorname{Spec}$ of $R \to T$; these bijections are assumed multiplicative (carrying the convolution product to the group law) and natural in $T$ (for $a : T \to T'$ an $R$-algebra map, the point attached to $a \circ \phi$ is $\operatorname{Spec} a$ followed by the point attached to $\phi$). The conclusion is the existence of an $R$-bialgebra homomorphism $\varphi : H_J \to H_B$ such that for every commutative $R$-algebra $T$ and every $x \in H_B \to_{R\text{-alg}} T$, the $n$-torsion point of $L$ attached to $x \circ \varphi$ equals the $n$-torsion point of $L_B$ attached to $x$ post-composed with $u$.
--
--   This is the Yoneda-style functoriality statement for the Hopf algebras corepresenting $n$-torsion of relative group laws: a homomorphism of group laws induces a bialgebra map in the opposite direction, acting on points by composition. It is used in the construction of the Hecke action on finite flat models of torsion subschemes of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_torsion_of_hom
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (n : ℕ)
    (HB : Type u) [CommRing HB] [HopfAlgebra R HB] (HJ : Type u) [CommRing HJ] [HopfAlgebra R HJ]
    (eB : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HB →ₐ[R] T) ≃
          LB.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eB_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HB →ₐ[R] T)),
        ((eB T (φ * ψ)).val : SchemeHomOver _ g) =
          LB.mul _ (eB T φ).val (eB T ψ).val)
    (eB_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HB →ₐ[R] T)),
        ((eB T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ g).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eB T φ).val.1)
    (eJ : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HJ →ₐ[R] T) ≃
          L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eJ_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HJ →ₐ[R] T)),
        ((eJ T (φ * ψ)).val : SchemeHomOver _ f) =
          L.mul _ (eJ T φ).val (eJ T ψ).val)
    (eJ_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HJ →ₐ[R] T)),
        ((eJ T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eJ T φ).val.1) :
    ∃ φ : HJ →ₐc[R] HB, ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      ((eJ T (.toConv (x.ofConv.comp (φ : HJ →ₐ[R] HB)))).val : SchemeHomOver _ f) =
        NeronModelInfra.schemeHomOverComp ((eB T x).val : SchemeHomOver _ g) u := by sorry
