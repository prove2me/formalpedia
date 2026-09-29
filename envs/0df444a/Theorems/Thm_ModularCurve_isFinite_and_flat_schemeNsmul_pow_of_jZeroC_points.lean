-- Prove2me | Theorems.Thm_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
-- name    : ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/543c26b1-c0da-504e-8641-7d61c990637b
-- title:
--   Finite flatness of [ℓ^k] on a model of J₀(p)
-- statement:
--   Let $p \ge 1$ be a natural number and $\ell$ a prime with $\ell \nmid p$, and write $R = \mathbf{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. Let $f : J \to \operatorname{Spec} R$ be a morphism of schemes equipped with a `RelativeGroupLaw` $L$: a group structure, natural in the base change $T \to \operatorname{Spec} R$, on the sets $\{\varphi : T \to J \mid \varphi \text{ followed by } f \text{ equals } t\}$ of $T$-points of $J$ over $R$. Assume `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that the fibre $f^{-1}(s)$ over each point $s$ of $\operatorname{Spec} R$ is connected, and that $f$ admits some relative group law; assume also that $L$ is commutative on $T$-points for every $T$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ lying over $\ell$, in the sense that the image of $\ell$ is a non-unit of $A$, let $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec} R$ be a morphism, and suppose given a bijection between $\mathrm{Pic}^0$ of the modular function field `modularFunctionFieldFullC` of level $p$ over the residue field $\kappa_A$ of $A$ and the set of points of $J$ over the composite $\operatorname{Spec} \kappa_A \to \operatorname{Spec} A \to \operatorname{Spec} R$, carrying addition of divisor classes to the multiplication of $L$. Then for every $k$ the endomorphism $L.\mathrm{schemeNsmul}(\ell^k) : J \to J$, the underlying morphism of the $\ell^k$-fold $L$-sum of the identity point of $J$, is finite and flat.
--
--   This is the finite flatness of multiplication by $\ell^k$ on an abelian scheme, in the form needed for a smooth proper model over $\mathbf{Z}_{(\ell)}$ of the Jacobian $J_0(p)$ with $\ell \nmid p$: the hypothesis identifying the $\kappa_A$-points with the degree-zero divisor class group of the modular function field in characteristic $\ell$ supplies finiteness of the $\ell^k$-torsion on the special fibre, where multiplication by $\ell^k$ fails to be étale. It is used to produce finite flat models of the $\ell$-power torsion of $J_0(p)$, and through these the Hecke- and Frobenius-compatible statements about the associated finite flat group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hJ : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (ptsSp : JZeroC (ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f)
    (hadd : ∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v))
    (k : ℕ) :
    IsFinite (L.schemeNsmul (ℓ ^ k)) ∧ Flat (L.schemeNsmul (ℓ ^ k)) := by sorry
