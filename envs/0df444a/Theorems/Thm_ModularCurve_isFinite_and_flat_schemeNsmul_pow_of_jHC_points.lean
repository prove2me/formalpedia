-- Prove2me | Theorems.Thm_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jHC_points
-- name    : ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jHC_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/96c2fe5e-fd79-59ec-b1eb-449f6eb5d120
-- title:
--   Finiteness and flatness of [ℓ^k] on an abelian ℤ_{(ℓ)}-scheme
-- statement:
--   Fix an integer $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a prime $\ell$ not dividing $M$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $f \colon J \to \operatorname{Spec} \mathbb{Z}_{(\ell)}$ be a morphism of schemes, equipped with a `RelativeGroupLaw` $L$: a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on each set $\{\varphi \colon T \to J \mid \varphi \text{ followed by } f = t\}$ of $J$-points over a $\mathbb{Z}_{(\ell)}$-scheme $t \colon T \to \operatorname{Spec} \mathbb{Z}_{(\ell)}$, natural in $T$ under precomposition. Assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, each set-theoretic fibre of $f$ over a point of $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ is connected, and $f$ admits some relative group law; assume further that $L$ is commutative on points of every test scheme. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, let $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(\ell)}$ be a morphism, and suppose given a bijection, additive for $L$'s multiplication, between the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the $q$-expansion function field `xHFunctionFieldC` attached to $\Gamma_H(M)$ over the residue field of $A$ and the set of $J$-points over the composite of $\operatorname{Spec}$ of the residue map with $\sigma_A$. Then for every $k$ the endomorphism $L.\mathrm{schemeNsmul}\,(\ell^{k})$ of $J$, namely the first component of the $\ell^{k}$-fold $L$-sum of the identity point of $J$ over itself, is a finite morphism and is flat.
--
--   Classically this is the statement that multiplication by a positive integer on an abelian scheme is a finite flat morphism, here for $[\ell^{k}]$ on a smooth proper commutative group scheme over $\mathbb{Z}_{(\ell)}$ whose special-fibre points are identified with the degree-zero divisor classes of the characteristic-$\ell$ $q$-expansion field of $X_H(M)$. It feeds the quasi-finite, quasi-compact and flat properties of $[\ell^{k}]$ on the Néron-type model of $J_H(M)$ at $\ell$, and the surjectivity of reduction on $\ell^{k}$-torsion used in the $q$-expansion comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jHC_points.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jHC_points
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hJ : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (ptsSp : JHC M H (ResidueField ↥A) ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f)
    (hadd : ∀ u v : JHC M H (ResidueField ↥A), ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v))
    (k : ℕ) :
    IsFinite (L.schemeNsmul (ℓ ^ k)) ∧ Flat (L.schemeNsmul (ℓ ^ k)) := by sorry
