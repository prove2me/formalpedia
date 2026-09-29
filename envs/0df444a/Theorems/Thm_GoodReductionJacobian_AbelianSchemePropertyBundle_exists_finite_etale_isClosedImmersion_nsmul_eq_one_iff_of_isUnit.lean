-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_etale_isClosedImmersion_nsmul_eq_one_iff_of_isUnit
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_isClosedImmersion_nsmul_eq_one_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/12b609f2-23d1-510e-b95c-cb8ae9edb958
-- title:
--   n-torsion of an abelian scheme is finite étale
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ on $f$, that is, functorially compatible multiplication, unit and inverse operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over arbitrary $S$-schemes $t : T \to \operatorname{Spec} S$, satisfying the group axioms and natural in $T$; assume $L$ is commutative, and that $f$ satisfies the property bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $g : \mathbb{N}$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $n \ge 1$ with the image of $n$ in $S$ a unit. Then there exists a commutative ring $B$ with an $S$-algebra structure making it finite as an $S$-module and étale over $S$, together with a morphism $\iota : \operatorname{Spec} B \to A$ over $\operatorname{Spec} S$ (i.e. $\iota$ followed by $f$ equals the structure morphism $\operatorname{Spec} B \to \operatorname{Spec} S$) which is a closed immersion, such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every section $y$ of $f$ over $t$, the $n$-fold multiple $L.\mathrm{nsmul}\,t\,n\,y$ equals the unit section $L.\mathrm{one}\,t$ if and only if $y$ factors as $z$ followed by $\iota$ for some $z : T \to \operatorname{Spec} B$.
--
--   This is the statement that the $n$-torsion subscheme $A[n]$ of an abelian scheme over an arbitrary base, with $n$ invertible on the base, is a finite étale closed subscheme, presented as a dictionary of points rather than via an explicit kernel construction; the fibre dimension $g$ is recorded but no rank assertion is made. It is the rank-free form used by the companion statement [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_rankAtStalk_eq_pow_nsmul_eq_one_iff_of_isUnit), which adds the rank $n^{2g}$, and it underlies the construction of the Galois representations on torsion of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_etale_isClosedImmersion_nsmul_eq_one_iff_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_etale_isClosedImmersion_nsmul_eq_one_iff_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit ((n : ℕ) : S)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (_ : Module.Finite S B) (_ : Algebra.Etale S B)
      (ι : Spec (CommRingCat.of B) ⟶ A) (_ : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B))) (_ : IsClosedImmersion ι),
      ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
        L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1 := by sorry
