-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
-- name    : ModularCurve.FullLevel.isDomain_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/4b6cf1dd-09fa-5790-a1a3-ae16a8a61b9d
-- title:
--   Geometric integrality of components of the full-level moduli ring
-- statement:
--   Let $A$ be a discrete valuation domain, $q\ge 5$ and $\ell\ge 3$ distinct primes, $M'\neq 0$ a natural number with $q\nmid M'$ and $\ell\nmid M'$, and suppose $q$ lies in the maximal ideal of $A$ while $\ell$ and $M'$ are units in $A$. Let $K'$ be a fraction field of $A$ of characteristic $0$, let $r\in A$ be such that its image in $K'$ is a primitive $(q\ell)$-th root of unity, and assume there is a ring embedding $\iota:K'\to\mathbb{C}$ carrying that image to $\exp(2\pi i/(q\ell))$; let $L$ be a field extension of $K'$, viewed as an $A$-algebra compatibly. Assume: level-$\ell$ structures in the sense of `IsLevelPStructure` (two affine points $P,Q$ killed by $\operatorname{pre}\Psi_\ell$ with both independence elements units) are preserved by variable change; the $\Gamma_0$-prime-power kernel-generator conditions `IsGamma0PowAt` are preserved by variable change via `kernelVariableChangeDeg`; $\mathcal{G}$ is a family of relative group laws on the projective Weierstrass models over $A$-algebras with invertible discriminant, chord-tangent (compatible with a points-evaluation identification) and with origin section given by the origin chart; $\mathcal{T}$ is a transport of Drinfeld pairs at $q$ satisfying `IsSectionTransport`; and variable changes, respectively coefficient maps, are realised by graded ring homomorphisms of the projective-model gradings satisfying `IsVariableChangeHom`, respectively `IsCoefficientHom`, with the stated condition on irrelevant ideals. Let $P_0$ be a fine moduli package for the moduli datum attached to `rigidDataPow`, that is, an $A$-algebra $B_0$ with a universal point of the functor of curves with unit discriminant equipped with a $\Gamma_0(M')$-tuple of prime-power kernel generators, a level-$\ell$ structure and a Drinfeld $\Gamma(q)$-basis, up to variable change, such that every such point over an $A$-algebra $T$ comes from a unique $A$-algebra map $B_0\to T$; assume $B_0$ is of finite type over $A$. Then for every minimal prime $\mathfrak{p}$ of the zero ideal of $B_0$, the tensor product $L\otimes_A (B_0/\mathfrak{p})$ is an integral domain.
--
--   The assertion is that the irreducible components of the fine moduli ring for $\Gamma_0(M')\times\Gamma(\ell)\times$ Drinfeld-$\Gamma(q)$ structures remain integral after any extension of the constants once $\zeta_{q\ell}$ lies in the base field. It is used in the analysis of the special fibre, where reducedness of the residue-field base change of such quotients is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isDomain_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (K' : Type) [Field K'] [CharZero K'] [Algebra A K'] [IsFractionRing A K']
    (r : A) (hr : IsPrimitiveRoot (algebraMap A K' r) (q * ℓ))
    (hιξ' : ∃ ι : K' →+* ℂ, ι (algebraMap A K' r) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (L : Type) [Field L] [Algebra K' L] [Algebra A L] [IsScalarTower A K' L]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    IsDomain (TensorProduct A L (P₀.B₀ ⧸ 𝔭)) := by sorry
