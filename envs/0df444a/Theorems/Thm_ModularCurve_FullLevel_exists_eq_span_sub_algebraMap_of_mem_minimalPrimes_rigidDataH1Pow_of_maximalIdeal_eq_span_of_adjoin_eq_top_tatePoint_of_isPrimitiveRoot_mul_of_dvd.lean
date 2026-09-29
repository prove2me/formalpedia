-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_eq_span_sub_algebraMap_of_mem_minimalPrimes_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.exists_eq_span_sub_algebraMap_of_mem_minimalPrimes_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/e61aa904-3451-527e-b405-9d69bd642540
-- title:
--   Minimal primes of the level moduli ring are principal pins
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero carrying a primitive $(q\ell)$-th root of unity $\xi$ and a ring embedding $\iota : L \to \mathbb{C}$ with $\iota(\xi) = e^{2\pi i/(q\ell)}$; let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K \subseteq L((t))$ be the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. Further data: a discrete valuation domain $A$ with fraction field $L$ and $q$ in its maximal ideal, acting on $K$ compatibly; an element $j \in K$ whose Laurent expansion is the image of the $j$-series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed nonzero; a discrete valuation domain $A_0$ with maximal ideal $(q)$, finite below $A$ and compatible with $K$, such that $A$ is generated over $A_0$ by an element $\zeta_A$ whose image in $L$ is a primitive $q$-th root of unity, $A_0$ contains a primitive $\ell$-th root of unity, and $\ell$, $M'$ are units in $A_0$. Next, three variable-change equivariance hypotheses (for $\Gamma_1(\ell)$-points, for the $\Gamma_0$ prime-power kernel-polynomial predicate, and for divisibility of `inLineMulPoly`), a family $\mathcal{G}$ of relative group laws on the projective Weierstrass models with unit discriminant which is chord–tangent and has the origin as identity, a level transport $\mathcal{T}$ of raw Drinfeld pairs at $q$ satisfying the section-transport compatibilities, and the existence of graded homomorphisms on the projective coordinate rings realising variable changes and coefficient maps (all summarised here). Let $P_0$ be an abstract fine moduli package, with ring $B_0$ and universal point, for the moduli datum of the rigid data `rigidDataH1Pow` built from these level components, and let $x$ be a $K$-point of that datum whose $j$-invariant has Laurent expansion [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18). Then for every minimal prime $\mathfrak{p}$ over $(0)$ in $B_0$ there are $b \in B_0$ and $a \in A_0$ with $b^\ell = 1$, $a^\ell = 1$ and $\mathfrak{p} = (b - a)B_0$.
--
--   This is the pinning statement for the minimal primes of the ring $B_0$ representing the rigidified $\Gamma_0(M')$–$\Gamma_1(\ell)$–Drinfeld-$q$ moduli problem in the $\Gamma_1(\ell)$ auxiliary frame, each such prime being cut out by a single difference of $\ell$-th roots of unity. It is used in bounding the kernel of the classifying map on prime ideals of $B_0$ for points with $j$-invariant the Tate $q$-expansion `jqNModC L q`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_eq_span_sub_algebraMap_of_mem_minimalPrimes_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd.lean

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
import Definitions.Def_ModularCurve_WeierstrassH1Pow
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

theorem ModularCurve.FullLevel.exists_eq_span_sub_algebraMap_of_mem_minimalPrimes_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')

    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})

    [Algebra A₀ ↥K] [Algebra A₀ A] [IsScalarTower A₀ A ↥K] [Module.Finite A₀ A]
    (ζA : A) (hζA : IsPrimitiveRoot (algebraMap A L ζA) q) (hA₀A : Algebra.adjoin A₀ ({ζA} : Set A) = ⊤)

    (hω : ∃ ω : A₀, IsPrimitiveRoot ω ℓ)

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q)

    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    ∃ (b : P₀.B₀) (a : A₀), b ^ ℓ = 1 ∧ a ^ ℓ = 1 ∧ 𝔭 = Ideal.span {b - algebraMap A₀ P₀.B₀ a} := by sorry
