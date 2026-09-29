-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_gamma0Pow
-- name    : ModularCurve.FullLevel.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/dc078950-ef20-552e-929b-6125d2b77cff
-- title:
--   Integral closedness of the q-expansion image of the moduli ring
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and an integer $M'\neq 0$ divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$ for which some ring homomorphism $L\to\mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell))$, and let $K$ be the intermediate field of $L(\!(\mathsf q)\!)$ obtained by adjoining to $L$ the image, under coefficientwise extension along $\mathbb{Q}\to L$, of the $q$-expansion function field of the curve of level $\Gamma_H((q\ell)^2M')$ with $H$ the kernel of the reduction map $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/(q\ell))^\times$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in the maximal ideal of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be the element whose Laurent series is the coefficientwise image of the $q$-expansion of the modular $j$-function, assumed nonzero; $\ell$ and $M'$ are assumed invertible in $A$. Assume further: level-$\ell$ structures in the sense of [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) and prime-power generator-kernel data in the sense of [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) are stable under Weierstrass variable change (via `LevelPData.variableChange` and `kernelVariableChangeDeg`); a family $\mathcal{G}$ of relative group laws on the projective Weierstrass models over $A$-algebras which is chord–tangent (realised on points of fields) and has the unit section supported at the origin chart; a transport $\mathcal{T}$ of Drinfeld pairs along $A$-algebra maps and variable changes compatible with $\mathcal{G}$-Drinfeld bases at $q$, whose sections transport correctly along the graded homomorphisms; and existence of graded homomorphisms realising variable changes and coefficient maps on the homogeneous coordinate rings. Let $P_0$ be a fine moduli package (a representing $A$-algebra $B_0$ of finite type with universal point) for the moduli datum attached to the product level component combining the $\Gamma_0$-power data at $M'$, the level-$\ell$ data and the Drinfeld level-$q$ data, and let $\iota:B_0\to K$ be an $A$-algebra homomorphism such that $\iota(j_0)$ is integral over $A[j]$, $j$ is integral over $A[\iota(j_0)]$, and every element of $K$ is a quotient $\iota(x)/\iota(y)$ with $\iota(y)\neq 0$. Then every $x\in K$ integral over the range of $\iota$ lies in the range of $\iota$.
--
--   This is the normality half of the identification of the range of the classifying map with the $j$-finite chart algebra: the image of the fine moduli ring of the rigidified full-level problem inside the $q$-expansion field is integrally closed there. It is used by [`ModularCurve.FullLevel.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow`](thm.html#ModularCurve.FullLevel.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_gamma0Pow
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
    (ι : P₀.B₀ →ₐ[A] ↥K)
    (hι : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) (ι P₀.j₀))
    (hι' : IsIntegral ↥(Algebra.adjoin A ({ι P₀.j₀} : Set ↥K)) j)
    (hdense : ∀ k : ↥K, ∃ x y : P₀.B₀, ι y ≠ 0 ∧ k * ι y = ι x) :
    ∀ x : ↥K, IsIntegral ↥ι.range x → x ∈ ι.range := by sorry
