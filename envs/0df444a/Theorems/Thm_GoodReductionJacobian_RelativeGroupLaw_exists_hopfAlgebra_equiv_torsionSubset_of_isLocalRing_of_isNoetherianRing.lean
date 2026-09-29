-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_equiv_torsionSubset_of_isLocalRing_of_isNoetherianRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_equiv_torsionSubset_of_isLocalRing_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/05fef121-b332-50cd-bbf0-520a5ca63e55
-- title:
--   Representability of n-torsion by a finite free Hopf algebra
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism, and let $L$ be a relative group law for $f$: a functorial group structure, for every $S$-scheme $t\colon T\to\operatorname{Spec}S$, on the set of sections $\{\varphi\colon T\to A \mid \varphi \text{ followed by } f = t\}$, with multiplication, unit and inverse satisfying associativity, unit and left inverse laws and compatible with precomposition in $T$. Assume the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, every fibre of $f$ over a point of $\operatorname{Spec}S$ is connected, and a relative group law for $f$ exists. Let $n$ be a nonzero natural number, let $R$ be a noetherian local commutative ring and let $\iota\colon\operatorname{Spec}R\to\operatorname{Spec}S$ be a morphism. Then there exists a commutative ring $H$ carrying a Hopf $R$-algebra structure, finite and free as an $R$-module and with cocommutative comultiplication, together with bijections, for every commutative $R$-algebra $T$, $$e_T\colon\ \mathrm{WithConv}(H\to_{\mathrm{alg}[R]}T)\ \xrightarrow{\ \sim\ }\ \{x \mid L.\mathrm{nsmul}\ n\ x = L.\mathrm{one}\},$$ from the $R$-algebra homomorphisms $H\to T$ with their convolution product to the set of sections of $f$ over the composite of $\operatorname{Spec}$ of $R\to T$ with $\iota$ that are killed by $n$ for the group law $L$, such that (i) $e_T(\varphi\psi)$ is the $L$-product of $e_T(\varphi)$ and $e_T(\psi)$, and (ii) for every $R$-algebra map $g\colon T\to T'$ and every $\varphi$, the section underlying $e_{T'}(g\circ\varphi)$ is $\operatorname{Spec}(g)$ followed by the section underlying $e_T(\varphi)$. No statement is made about the rank of $H$ over $R$.
--
--   This is the representability of the $n$-torsion of an abelian scheme by a finite locally free commutative cocommutative Hopf algebra, specialised to a noetherian local test ring, where local freeness becomes freeness. It is the input to [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing), where points of the torsion scheme are matched with characters of the Cartier dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_equiv_torsionSubset_of_isLocalRing_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_equiv_torsionSubset_of_isLocalRing_of_isNoetherianRing
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (n : ℕ) (hn : n ≠ 0)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H) (_ : Module.Finite R H) (_ : Module.Free R H)
      (_ : Coalgebra.IsCocomm R H)
      (e : ∀ (T : Type) [CommRing T] [Algebra R T],
        WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι) n),
      (∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
        ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
          (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
        ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by sorry
