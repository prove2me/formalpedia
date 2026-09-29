-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ker_classify_mem_minimalPrimes_of_jOf_eq_jqNModC_gamma0Pow
-- name    : ModularCurve.FullLevel.ker_classify_mem_minimalPrimes_of_jOf_eq_jqNModC_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/0a471a69-887a-5ba4-a73b-bc73b6cad2eb
-- title:
--   Kernel of the classifying map at j(q^{qℓ}) is minimal
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and a nonzero natural number $M'$ divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$, assumed to admit a ring homomorphism $L\to\mathbb{C}$ carrying $\xi$ to $\exp(2\pi i/(q\ell))$, and let $K$ be the intermediate field of $L\subseteq\operatorname{LaurentSeries} L$ obtained by adjoining to $L$ the image, under coefficientwise extension along $\mathbb{Q}\to L$, of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$ with $H$ the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\ell$ and $M'$ units in $A$, acting on $K$ compatibly with the tower, and let $j\in K$ be the element whose Laurent series is the coefficient extension of the $q$-expansion $q^{-1}\cdot(\text{integral }j\text{-numerator})$, assumed nonzero. Assume: variable-change stability of level-$\ell$ Katz structures (equations, vanishing of $\operatorname{pre}\Psi_\ell$ at both points, and invertibility of both independence elements) and of the $\Gamma_0(p^k)$ cyclic-kernel polynomial data; a family $\mathcal{G}$ of relative group laws on the projective Weierstrass models over $A$-algebras which is chord-tangent and has the origin as identity; a level transport $\mathcal{T}$ for Drinfeld $q$-bases compatible with the sections; and existence of graded ring homomorphisms realising variable changes ($hVC$) and coefficient maps ($hCO$) on the projective models. Let $P_0$ be a fine moduli package, with coordinate ring $B_0$ of finite type over $A$, for the level moduli datum attached to the rigidified product component combining $\Gamma_0$-power kernel polynomials for $M'$, level-$\ell$ structure and Drinfeld $q$-level structure. Then for any $K$-point $x$ of this datum whose $j$-invariant has Laurent series equal to $j$ expanded in $q^{q\ell}$, the kernel of the underlying ring homomorphism of the classifying $A$-algebra map $B_0\to K$ determined by $x$ is a minimal prime of $B_0$.
--
--   The statement says that any $K$-point lying over the Tate-type $j$-value $j(\mathfrak{q}^{q\ell})$ classifies into a single irreducible component of the fine moduli scheme: its classifying map kills exactly a minimal prime, because $B_0$ is integral over the image of the $j$-line and the composite is injective there. It is used by the statements counting the minimal primes of $B_0$ and producing algebra equivalences identifying the components, i.e. in the component analysis of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ker_classify_mem_minimalPrimes_of_jOf_eq_jqNModC_gamma0Pow.lean

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
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.ker_classify_mem_minimalPrimes_of_jOf_eq_jqNModC_gamma0Pow
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
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ)) :
    RingHom.ker (P₀.classify x).toRingHom ∈ (⊥ : Ideal P₀.B₀).minimalPrimes := by sorry
