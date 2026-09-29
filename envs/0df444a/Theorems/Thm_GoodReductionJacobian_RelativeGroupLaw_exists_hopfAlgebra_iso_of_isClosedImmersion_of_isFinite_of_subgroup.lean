-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/45e23b6e-2323-5239-96a1-e57654b44319
-- title:
--   Finite closed subgroup of a relative group law is Spec of a Hopf algebra
-- statement:
--   Let $k$ be a field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$: for each $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the two unit laws, left inverse, and compatibility of multiplication with precomposition along morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative on all $T$-points, and let $\iota : C \to A$ be a closed immersion with $\iota$ followed by $f$ finite, such that for every $k$-scheme $T$ the $T$-points of $A$ factoring through $\iota$ form a subgroup: the unit point factors through $\iota$, and if $P$ and $Q$ factor through $\iota$ then so do $L.\mathrm{mul}\,P\,Q$ and $L.\mathrm{inv}\,P$. Then there exists a commutative ring $H$ carrying a Hopf $k$-algebra structure, finite as a $k$-module and cocommutative, together with a morphism $j : \operatorname{Spec} H \to C$ and, for every commutative $k$-algebra $T$, a map $e_T$ from $k$-algebra homomorphisms $H \to T$ with their convolution multiplication to the set of $T$-points of $A$ (over $\operatorname{Spec}$ of $k \to T$) factoring through $\iota$, such that: $j$ is an isomorphism; $j$ followed by $\iota$ followed by $f$ is $\operatorname{Spec}$ of $k \to H$; $e_T(\varphi)$ is $\operatorname{Spec}\varphi$ followed by $j$ followed by $\iota$; each $e_T$ is bijective; $e_T(\varphi\psi) = L.\mathrm{mul}\,(e_T\varphi)\,(e_T\psi)$; and for a $k$-algebra map $g : T \to T'$, $e_{T'}(g \circ \varphi)$ is $\operatorname{Spec} g$ followed by $e_T(\varphi)$.
--
--   This is the Hopf-algebra form of the statement that a finite closed subgroup-functor of a commutative relative group law over a field is an affine group scheme, namely $\operatorname{Spec}$ of a finite commutative cocommutative Hopf algebra, together with the full dictionary between algebra homomorphisms out of $H$ under convolution and the subgroup of points. It matches the dictionary clauses of [`GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing), which the proof cites, and it is used in the characterisation of Frobenius kernels for fake elliptic curves in the Čerednik–Drinfeld setting and in an isomorphism criterion for proper group laws in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
    {k : Type u} [Field k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {C : Scheme.{u}} (ι : C ⟶ A) [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)), ∃ P₀ : T ⟶ C, P₀ ≫ ι = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      (∃ P₀ : T ⟶ C, P₀ ≫ ι = P.1) → (∃ Q₀ : T ⟶ C, Q₀ ≫ ι = Q.1) →
        (∃ R₀ : T ⟶ C, R₀ ≫ ι = (L.mul t P Q).1) ∧ (∃ S₀ : T ⟶ C, S₀ ≫ ι = (L.inv t P).1)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H),
      Module.Finite k H ∧ Coalgebra.IsCocomm k H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ C)
        (e : ∀ (T : Type u) [CommRing T] [Algebra k T],
          WithConv (H →ₐ[k] T) →
            {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T))) f // ∃ P₀ : _ ⟶ C, P₀ ≫ ι = P.1}),
        IsIso j ∧

        j ≫ ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H)) ∧

        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ : WithConv (H →ₐ[k] T)),
          ((e T φ).val : SchemeHomOver _ f).1 = Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫ ι) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T], Function.Bijective (e T)) ∧

        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧

        (∀ (T T' : Type u) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
            (g : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by sorry
