-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_rankAtStalk_eq_pow_of_nsmul_eq_one_iff_of_isUnit
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.rankAtStalk_eq_pow_of_nsmul_eq_one_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/5590b56c-0416-5671-a92e-e33c75a5e0ac
-- title:
--   Rank n^{2g} of the n-torsion subscheme of an abelian scheme
-- statement:
--   Let $S$ be a commutative ring, let $f : A \to \operatorname{Spec} S$ be a morphism of schemes, and let $L$ be a relative group law for $f$: a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for every $t : T \to \operatorname{Spec} S$, compatible with composition in $T$. Assume $L$ is commutative, and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Assume every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $n > 0$ with the image of $n$ a unit in $S$. Let $B$ be a finite étale $S$-algebra and $\iota : \operatorname{Spec} B \to A$ a closed immersion over $\operatorname{Spec} S$ such that, for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every section $y$ of $f$ over $t$, the $n$-fold $L$-power of $y$ equals the unit section precisely when $y$ factors through $\iota$. Then for every prime $\mathfrak p$ of $S$ one has $\operatorname{rank}_{\mathfrak p} B = n^{2g}$.
--
--   This is the classical statement that the $n$-torsion subscheme of an abelian scheme of relative dimension $g$, for $n$ invertible on the base, is finite étale of constant rank $n^{2g}$, here in the form: any finite étale closed subscheme representing the $n$-torsion has rank $n^{2g}$ at every prime. It is used to supply the rank assertion in the existence statement [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit), which produces the $n$-torsion subscheme together with its rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_rankAtStalk_eq_pow_of_nsmul_eq_one_iff_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.rankAtStalk_eq_pow_of_nsmul_eq_one_iff_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit ((n : ℕ) : S))
    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B))) (hιc : IsClosedImmersion ι)
    (hpts : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1) :
    ∀ p : PrimeSpectrum S, Module.rankAtStalk (R := S) B p = n ^ (2 * g) := by sorry
