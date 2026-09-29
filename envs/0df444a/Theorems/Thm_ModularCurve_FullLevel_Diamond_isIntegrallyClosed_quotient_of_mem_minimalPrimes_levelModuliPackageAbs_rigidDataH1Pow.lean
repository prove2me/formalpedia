-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b467bc2e-22e5-5fd2-8c10-72519bbfbb34
-- title:
--   Minimal-prime quotients of the H₁ moduli ring are normal
-- statement:
--   Let $q$ be a prime, $M'$ a non-zero natural number with $q \nmid M'$, and $\ell_g$ a prime with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $L$ be a field of characteristic zero, $\xi \in L$ a primitive $(q\ell_g)$-th root of unity such that some ring homomorphism $L \to \mathbb{C}$ carries $\xi$ to $\exp(2\pi i/(q\ell_g))$; let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^{\times}$ with the kernel of reduction to $(\mathbb{Z}/\ell_g)^{\times}$, and let $K$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field `xHFunctionField` of level $q^2M'$ and subgroup $H_1$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\ell_g$, $M'$ units in $A$, let $K$ be an $A$-algebra compatibly with $L$, and let $j \in K$ be an element, assumed non-zero, whose Laurent series is the image of the $q$-expansion `jq` of the $j$-invariant. Assume the three variable-change compatibilities `hℓ`, `hM`, `hL` over all $A$-algebras $T$: $\Gamma_1(\ell_g)$-point data stay $\Gamma_1(\ell_g)$-points under the induced change of data, the $\Gamma_0$-type condition `IsGamma0PowAt` at $(p,k)$ is preserved by `kernelVariableChangeDeg`, and divisibility of `inLineMulPoly` is preserved likewise. Let $\mathcal{G}$ assign to every $A$-algebra $T$ and projective Weierstrass curve $W/T$ with unit discriminant a relative group law on the graded $\mathrm{Proj}$ model of $W$, assumed chord-and-tangent (realised by a bijection with affine points over fields that is additive and Galois-equivariant) and with identity section the origin chart section at which $x/y$ and $z/y$ vanish; let $\mathcal{T}$ be a level transport of raw Drinfeld pairs for $\mathcal{G}$ and $q$, assumed to be a section transport, and assume that graded ring homomorphisms realising variable changes (`hVC`) and coefficient changes (`hCO`) of projective models exist, with the indicated inequality on irrelevant ideals. Let $P_0$ be a package representing the moduli datum of the rigid data `rigidDataH1Pow` — curves with unit discriminant equipped with a cyclic-kernel polynomial for each prime factor of $M'$, a $\Gamma_1(\ell_g)$-point with $P = Q$, and a Drinfeld $q$-basis, subject to the linkage that the $\ell_g$-component polynomial divides $\mathrm{inLineMulPoly}$ at $x_P$, points taken modulo variable change — so that its ring $B_0$ is an $A$-algebra carrying a universal point through which every point over an $A$-algebra factors uniquely. Assume $B_0$ is of finite type over $A$, and let $\mathfrak{p}$ be a minimal prime over $(0)$ in $B_0$. Then $B_0/\mathfrak{p}$ is integrally closed.
--
--   This is the normality statement for the irreducible components of the fine moduli ring of the rigid level datum combining $\Gamma_0$-type cyclic kernels at the primes of $M'$, a $\Gamma_1(\ell_g)$-point and a Drinfeld $q$-basis, over a discrete valuation ring in which $q$ is not invertible. It is obtained from flatness of $B_0$ over $A$, normality of the generic-fibre base change and reducedness of the residue-field fibre, and it feeds the integrality argument for $q$-expansions recorded in [`ModularCurve.FullLevel.Diamond.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    IsIntegrallyClosed (P₀.B₀ ⧸ 𝔭) := by sorry
