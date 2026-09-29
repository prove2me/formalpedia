-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/d1bc3c9f-af2c-500e-9fc5-4394dfac1fdc
-- title:
--   Components of the full-level moduli ring have reduced special fibre
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'\ge 1$ be an integer with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$, and assume there is a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L(\!(\mathsf q)\!)$ over $L$ obtained by adjoining to $L$ the image, under the coefficientwise map induced by $\mathbb Q\to L$, of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H\le(\mathbb Z/(q\ell)^2M')^\times$ is the kernel of reduction to $(\mathbb Z/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation ring with fraction field $L$ whose maximal ideal contains $q$, let $K$ be an $A$-algebra compatibly with the tower $A\to L\to K$, and let $j\in K$ be a nonzero element whose underlying Laurent series is the image of the $q$-expansion of the modular $j$-invariant. Assume $\ell$ and $M'$ are units in $A$; that level-$\ell$ structures (a pair of points satisfying the affine Weierstrass equation, with $\mathrm{pre}\Psi_\ell$ vanishing at both $x$-coordinates and both independence elements invertible) transform under a variable change $C$ into level-$\ell$ structures for $C\bullet W$ via [`ModularCurve.LevelPData.variableChange`](def/ModularCurve_KatzLevelP.html#L84); and that the predicate [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) at $(p,k)$ is preserved under variable change via [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104) in degree [`ModularCurve.gamma0PowDeg p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L53). Fix group laws $\mathcal G$ on the projective models of Weierstrass curves with unit discriminant over $A$-algebras which are chord–tangent (`IsChordTangent`) and normalised at the origin (`IsOriginIdentity`), and a level transport $\mathcal T$ for Drinfeld $q$-bases satisfying `IsSectionTransport`; assume moreover that every variable change and every coefficient change on a projective model is realised by a graded ring homomorphism of projective coordinate rings pulling back the irrelevant ideal as prescribed (`IsVariableChangeHom`, `IsCoefficientHom`). Let $P_0$ be a fine moduli package over $A$ for the moduli datum `rigidDataPow A ℓ M' q …` — the problem of a Weierstrass curve with unit discriminant equipped with a $\Gamma_0$-type kernel generator at each prime power dividing $M'$, a level-$\ell$ structure, and a Drinfeld $q$-basis, taken modulo variable change — so that $P_0$ consists of an $A$-algebra $B_0$ with a universal point represented by a unique $A$-algebra map into each test ring, and assume $B_0$ is of finite type over $A$. Then for every minimal prime $\mathfrak p$ of $B_0$ the ring $\kappa(A)\otimes_A(B_0/\mathfrak p)$, where $\kappa(A)$ is the residue field of $A$, is reduced.
--
--   This is the multiplicity-one half of the Katz–Mazur description of the reduction of the Drinfeld full level-$q$ moduli scheme: over a discrete valuation ring whose residue characteristic is $q$ and which contains the relevant roots of unity, each irreducible component of the fine moduli ring of $\Gamma_0$-tuple $\times\ \Gamma(\ell)\times$ Drinfeld-$\Gamma(q)$ structures has reduced special fibre. It feeds the proof that each such component is integrally closed, and is used in the local analysis of the charts of the full-level curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
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
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A) (P₀.B₀ ⧸ 𝔭)) := by sorry
