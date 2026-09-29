-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/379ca197-c3e5-5ee7-98c5-202416f0f733
-- title:
--   Hopf algebra of n-torsion when [n] is finite flat
-- statement:
--   Let $R$ be a commutative ring, $J$ a scheme and $f\colon J\to\operatorname{Spec}R$ a morphism, and let $L$ be a relative group law for $f$: for every $t\colon T\to\operatorname{Spec}R$ a multiplication, unit and inversion on the set $\{\varphi\colon T\to J \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $J$ over $t$, satisfying associativity, the two unit laws and left inversion, with multiplication natural under precomposition by morphisms $T'\to T$ over $\operatorname{Spec}R$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}\,t\,x\,y=L.\mathrm{mul}\,t\,y\,x$ for all $t$ and all $x,y$. Let $n\in\mathbb{N}$ and assume the endomorphism `L.schemeNsmul n` of $J$ — the underlying morphism of the $n$-fold $L$-sum of the identity point $\mathrm{id}_J\in J(J)$, formed by iterating $x\mapsto L.\mathrm{mul}$ from the unit — is finite and flat. Then there exist a type $H$ with a commutative ring structure and a Hopf $R$-algebra structure such that $H$ is finite and flat as an $R$-module, its comultiplication is cocommutative, and there is a family of bijections $e_T$, indexed by commutative $R$-algebras $T$, from the set $H\to_{\mathrm{alg}} T$ of $R$-algebra maps equipped with its convolution monoid structure (`WithConv`) onto the $n$-torsion subset $\{x\in J(T)\text{ over }\operatorname{Spec}(T)\to\operatorname{Spec}(R) \mid n\cdot_L x = L.\mathrm{one}\}$, such that (i) $e_T(\varphi\ast\psi)$ is, as a point of $J$ over $\operatorname{Spec}R$, the $L$-product of $e_T(\varphi)$ and $e_T(\psi)$, and (ii) for every $R$-algebra map $g\colon T\to T'$ and every $\varphi$, the underlying morphism of $e_{T'}(g\circ\varphi)$ is $\operatorname{Spec}(g)$ followed by the underlying morphism of $e_T(\varphi)$.
--
--   This realises the $n$-torsion of a commutative relative group law as a finite flat commutative group scheme over $\operatorname{Spec}R$, presented on the Hopf-algebra side together with its functor of points; finite flatness of multiplication by $n$ is taken as a hypothesis rather than derived from the theory of isogenies of abelian schemes. It is used to produce finite flat models of torsion in the Jacobian of modular curves, for instance in [`ModularCurve.exists_finiteFlat_model_jZero_torsion`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion), and in the construction of the associated $p$-divisible group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃
            L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n,
        (∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) =
            L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by sorry
