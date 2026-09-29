-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/0478b7cb-6d9d-5235-8f42-3523edfb1b42
-- title:
--   n-torsion of an abelian scheme is finite étale of rank n^{2g}
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$: an assignment, to every test scheme $T$ and morphism $t : T \to \operatorname{Spec} S$, of a multiplication, unit and inverse on the set of $T$-points $y : T \to A$ with $y \circ f = t$ (written `SchemeHomOver t f`), satisfying associativity, the unit laws, left inverses, and compatibility with base change along morphisms $T' \to T$ over $\operatorname{Spec} S$. Assume $L$ is commutative, that $f$ satisfies the property bundle consisting of smoothness, properness, connectedness of every fibre $f^{-1}(s)$ and the existence of some relative group law, and that for a natural number $g$ each fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $n$ be a positive integer whose image in $S$ is a unit. Then there is an $S$-algebra $B$ which is finite as an $S$-module and étale over $S$, with $\operatorname{rank}_{\mathfrak p} B = n^{2g}$ at every prime $\mathfrak p$ of $S$, together with a closed immersion $\iota : \operatorname{Spec} B \to A$ over $\operatorname{Spec} S$ (i.e. $\iota$ followed by $f$ equals the structure morphism $\operatorname{Spec} B \to \operatorname{Spec} S$), such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $y$ of $A$ over $t$, the $n$-fold iterate $n \cdot y$ (defined by repeated multiplication starting from the unit) equals the unit point if and only if $y$ factors as $z$ followed by $\iota$ for some $z : T \to \operatorname{Spec} B$.
--
--   This is the statement that the kernel of multiplication by $n$ on an abelian scheme of relative dimension $g$ is a finite étale closed subscheme of constant rank $n^{2g}$ over an arbitrary affine base on which $n$ is invertible, packaged as a dictionary identifying the $T$-points of that subscheme with the $n$-torsion $T$-points of $A$. It is used in the construction of level structures on polarised abelian schemes, via the passage to the finite étale group scheme of $n$-torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit ((n : ℕ) : S)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (_ : Module.Finite S B) (_ : Algebra.Etale S B)
      (_ : ∀ p : PrimeSpectrum S, Module.rankAtStalk (R := S) B p = n ^ (2 * g))
      (ι : Spec (CommRingCat.of B) ⟶ A) (_ : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B))) (_ : IsClosedImmersion ι),
      ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
        L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1 := by sorry
