-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f3c6d924-e5c1-5432-b809-7e08a6064517
-- title:
--   Components of the full-level moduli ring are normal
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M' \ne 0$ be a natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$, and assume there is a ring homomorphism $L \to \mathbb{C}$ carrying $\xi$ to $\exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$, assumed equal to [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2 M'$ for the subgroup [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22), i.e. the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$; thus $K$ is generated over $L$ by the coefficientwise images of that field of Laurent series over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in the maximal ideal of $A$, with $K$ an $A$-algebra compatibly with $A \to L \to K$, and let $j \in K$ be an element whose underlying Laurent series is the coefficient embedding of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-invariant, with $j \ne 0$. Assume $\ell$ and $M'$ are units in $A$. Assume two variable-change compatibilities: level-$\ell$ data satisfying [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) for $W$ remain such for $C \bullet W$ after `LevelPData.variableChange`, and polynomials satisfying [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $W$, $p$, $k$ remain such for $C \bullet W$ after [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104). Let $\mathcal{G}$ be a family of relative group laws on the projective Weierstrass models of curves with unit discriminant over $A$-algebras, satisfying `GroupLaws.IsChordTangent` (each group law admits a points-evaluation identifying it with affine addition on base changes to fields) and `GroupLaws.IsOriginIdentity` (its unit section comes from a homomorphism of the origin chart ring killing $x/y$ and $z/y$), and let $\mathcal{T}$ be a `LevelTransport` for $\mathcal{G}$ at $q$ satisfying `LevelTransport.IsSectionTransport`. Assume further that every variable change of a projective Weierstrass model over an $A$-algebra is realised by a graded ring homomorphism of the projective model rings satisfying `IsVariableChangeHom` and dominating the irrelevant ideal, and likewise that every $A$-algebra map is realised by one satisfying `IsCoefficientHom`. Finally let $P_0$ be an abstract fine moduli package for the moduli datum attached to `rigidDataPow A ℓ M' q`, that is, a finite-type $A$-algebra $B_0$ with a universal point representing the functor of variable-change classes of Weierstrass curves with unit discriminant equipped with generator-kernel polynomials for each prime power exactly dividing $M'$, a level-$\ell$ structure, and a Drinfeld basis of level $q$. Then for every minimal prime $\mathfrak{p}$ of the zero ideal of $B_0$, the quotient $B_0/\mathfrak{p}$ is integrally closed.
--
--   This is the normality statement for the irreducible components of the fine moduli ring of the rigidified full-level problem with a $\Gamma_0(M')$ slot in prime-power generator-kernel form: each component is a normal domain over the discrete valuation ring $A$. It is used in the proof that integral elements of the $q$-expansion image of the moduli ring lie in the range of the comparison map, where normality of the components is what permits integral elements to be recognised inside $B_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow
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
    IsIntegrallyClosed (P₀.B₀ ⧸ 𝔭) := by sorry
