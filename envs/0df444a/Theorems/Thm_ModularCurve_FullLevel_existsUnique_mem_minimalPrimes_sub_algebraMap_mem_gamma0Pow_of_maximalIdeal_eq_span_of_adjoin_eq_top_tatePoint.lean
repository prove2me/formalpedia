-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_existsUnique_mem_minimalPrimes_sub_algebraMap_mem_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint
-- name    : ModularCurve.FullLevel.existsUnique_mem_minimalPrimes_sub_algebraMap_mem_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/59ec1996-12fe-50fb-b128-c5b5eebe2290
-- title:
--   Unique minimal prime containing the Weil pin ξ_B - a
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and a nonzero natural number $M'$ divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$, and assume some ring homomorphism $L\to\mathbb{C}$ carries $\xi$ to $\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L\subseteq L((t))$ obtained as `laurentBaseChange`, the field generated over $L$ by the coefficientwise image of the $q$-expansion function field of level $(q\ell)^2M'$ attached to the subgroup $H\le(\mathbb{Z}/(q\ell)^2M')^\times$ of units congruent to $1$ modulo $q\ell$, this being the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$ in which $q$ lies in the maximal ideal, with an $A$-algebra structure on $K$ compatible with $L$, and let $j\in K$ be the element whose Laurent expansion is the image of the $q$-expansion `jq` of the modular invariant, $j\neq0$. Let $A_0$ be a discrete valuation domain with maximal ideal $(q)$, equipped with maps $A_0\to A\to K$ making $A$ a finite $A_0$-module, and suppose $A=A_0[\zeta]$ for an element $\zeta\in A$ whose image in $L$ is a primitive $q$-th root of unity; suppose moreover $A_0$ contains a primitive $\ell$-th root of unity and that $\ell$ and $M'$ are units in $A_0$. Assume the variable-change equivariance of level-$\ell$ structures (points $P,Q$ on $W$ with $\mathrm{pre}\Psi_\ell$ vanishing at their abscissae and invertible independence elements) and of the $\Gamma_0$-prime-power kernel polynomial conditions `IsGamma0PowAt`; let $\mathcal{G}$ be a family of relative group laws on the projective models of Weierstrass curves with invertible discriminant over $A_0$-algebras which is chord-tangent and has the origin as identity, and $\mathcal{T}$ a transport of Drinfeld $q$-bases compatible with sections; assume also the existence of graded homomorphisms of projective-model rings realising variable changes and coefficient changes (these last groups of hypotheses summarised here). Let $P_0$ be an abstract level moduli package over $A_0$ for the rigidified datum `rigidDataPow A₀ ℓ M' q …`, whose coordinate ring $B_0=P_0.B_0$ is of finite type over $A_0$, let $\xi_B\in B_0$ be a root of the $\ell$-th cyclotomic polynomial such that $B_0/(\xi_B-b)$ is nontrivial for every $b\in A_0$ with $b^\ell=1$, $b\neq1$, and such that for every field $F$ over $A_0$ with $\ell\neq0$ in $F$ and every point $y$ of the moduli datum over $F$ the classifying map sends $\xi_B$ to a primitive $\ell$-th root of unity. Finally let $x$ be a point of the moduli datum over $K$ whose $j$-invariant has Laurent expansion `jqNModC L (q*ℓ)`, the $j$-expansion in the variable $t^{q\ell}$, and let $a\in A_0$ satisfy $a^\ell=1$, $a\neq1$. Then there is exactly one ideal $\mathfrak{p}$ of $B_0$ which is a minimal prime of the zero ideal and contains $\xi_B-a$.
--
--   This is the statement that each value of the Weil-pairing coordinate $\xi_B$ at a nontrivial $\ell$-th root of unity cuts out a single generic component of the moduli ring $B_0$ of the rigidified level structure, the Tate point over $K$ serving to locate one component explicitly. It refines the companion result bounding the number of minimal primes of $B_0$ and containing the count $\varphi(\ell)$, and it is used to show that the quotient $B_0/(\xi_B-a)$ is a domain, the irreducibility input for the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_existsUnique_mem_minimalPrimes_sub_algebraMap_mem_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint.lean

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

theorem ModularCurve.FullLevel.existsUnique_mem_minimalPrimes_sub_algebraMap_mem_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint
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

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})

    [Algebra A₀ ↥K] [Algebra A₀ A] [IsScalarTower A₀ A ↥K] [Module.Finite A₀ A]
    (ζA : A) (hζA : IsPrimitiveRoot (algebraMap A L ζA) q) (hA₀A : Algebra.adjoin A₀ ({ζA} : Set A) = ⊤)

    (hω : ∃ ω : A₀, IsPrimitiveRoot ω ℓ)

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (ξB : P₀.B₀) (hξB : Polynomial.aeval ξB (Polynomial.cyclotomic ℓ A₀) = 0)
    (hnt : (∀ a : A₀, a ^ ℓ = 1 → a ≠ 1 → Nontrivial (P₀.B₀ ⧸ Ideal.span {ξB - algebraMap A₀ P₀.B₀ a})))
    (hweil : (∀ (F : Type) [Field F] [Algebra A₀ F] (y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt F),
        ((ℓ : ℕ) : F) ≠ 0 → IsPrimitiveRoot (P₀.classify y ξB) ℓ))
    [Algebra.FiniteType A₀ P₀.B₀]

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))

    (a : A₀) (ha : a ^ ℓ = 1) (ha1 : a ≠ 1) :
    ∃! 𝔭 : Ideal P₀.B₀, 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes ∧ ξB - algebraMap A₀ P₀.B₀ a ∈ 𝔭 := by sorry
