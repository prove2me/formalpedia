-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/63b3e14b-cac6-5b45-baf5-539343fa4520
-- title:
--   Normality of generic fibres of the full-level moduli ring
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and $M'\ge 1$ with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$ carrying a primitive $(q\ell)$-th root of unity $\xi$ whose image under some ring homomorphism $L\to\mathbb{C}$ is $e^{2\pi i/(q\ell)}$, let $K$ be the intermediate field of $L(\!(\mathsf q)\!)$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of the curve of level $(q\ell)^2M'$ with $H$ the kernel of $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, and let $j\in K$, nonzero, have underlying Laurent series the coefficientwise image of the $q$-expansion of the modular invariant. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal and $\ell$, $M'$ invertible in $A$, and with $K$ an $A$-algebra compatibly with $L$. Assume: level-$\ell$ structures and $\Gamma_0$-type prime-power kernel polynomials are stable under Weierstrass variable change (`hℓ`, `hM`); $\mathcal{G}$ is a family of relative group laws on the projective models of Weierstrass curves with unit discriminant over $A$-algebras which is chord-tangent and has the origin as identity; $\mathcal{T}$ transports raw Drinfeld pairs along $A$-algebra maps and variable changes, preserving the Drinfeld-basis condition, and does so compatibly with the induced maps of projective models (`h𝒯`); every variable change and every coefficient map is realised by a graded homomorphism of projective-model rings satisfying the stated irrelevant-ideal condition (`hVC`, `hCO`). Let $P_0$ be a fine moduli package for the resulting rigidified moduli problem, i.e. an $A$-algebra $B_0$ with a universal point uniquely classifying points over every $A$-algebra, with $B_0$ of finite type over $A$, and let $\mathfrak p$ be a minimal prime of $B_0$. Then $L\otimes_A(B_0/\mathfrak p)$ is an integral domain and is integrally closed.
--
--   The statement says that the generic fibre of each irreducible component of the fine moduli ring of the rigidified full-level problem (Drinfeld $q$-basis, level-$\ell$ structure, $\Gamma_0$-type prime-power kernels at the primes of $M'$) is a normal integral domain, the algebraic counterpart of the smoothness and normality of the characteristic-zero modular curve. It feeds the companion statement recording integral closedness alone, and thereby the identification of components of the full-level curve with their function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

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
    IsDomain (TensorProduct A L (P₀.B₀ ⧸ 𝔭)) ∧ IsIntegrallyClosed (TensorProduct A L (P₀.B₀ ⧸ 𝔭)) := by sorry
