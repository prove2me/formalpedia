-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_finite_minimalPrimes_and_ncard_le_sub_one_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_of_jOf_eq
-- name    : ModularCurve.FullLevel.finite_minimalPrimes_and_ncard_le_sub_one_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_of_jOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/6ac2d4ae-37a3-53d8-a933-698527a78124
-- title:
--   At most ℓ-1 minimal primes of the full-level moduli ring
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\ne q$, and a non-zero natural number $M'$ with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$ such that some ring homomorphism $L\to\mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell))$, and let $K$ be the intermediate field of $L\subseteq L(\!(T)\!)$ obtained by adjoining to $L$ the coefficientwise images under $\mathbb{Q}\to L$ of the $q$-expansion function field over $\mathbb{Q}$ of the modular curve $X_H$ of level $(q\ell)^2M'$, where $H\le(\mathbb{Z}/(q\ell)^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in its maximal ideal, acting on $K$ compatibly with $L$, and let $j\in K$ be a non-zero element whose image in $L(\!(T)\!)$ is the coefficientwise image of the $q$-expansion $\mathrm{jq}$ of the modular $j$-invariant. Let $A_0$ be a discrete valuation domain whose maximal ideal is $(q)$, with $A_0\to A\to K$ a tower, $A$ finite as an $A_0$-module, and $A=A_0[\zeta_A]$ for an element $\zeta_A\in A$ whose image in $L$ is a primitive $q$-th root of unity; assume $A_0$ contains a primitive $\ell$-th root of unity and that $\ell$ and $M'$ are units in $A_0$. Assume further: level-$\ell$ data (a quadruple $x_P,y_P,x_Q,y_Q$ satisfying the affine Weierstrass equation, with $\operatorname{pre}\Psi_\ell$ vanishing at both $x$-coordinates and both independence elements units) is carried by variable changes to level-$\ell$ data of the transformed curve; the analogous stability of the $\Gamma_0(p^k)$ kernel-generator condition under `kernelVariableChangeDeg`; a family $\mathcal{G}$ of relative group laws on the projective models of Weierstrass curves over $A_0$-algebras with unit discriminant which is chord-tangent and has the origin as identity section; a transport $\mathcal{T}$ of Drinfeld pairs at level $q$ which is a section transport; and the existence, for every variable change and every coefficient homomorphism, of graded ring maps of the projective-model rings realising them and satisfying the irrelevant-ideal condition. Let $P_0$ be an abstract representing package, with underlying ring $B_0$ of finite type over $A_0$, for the moduli problem `rigidDataPow` $A_0\,\ell\,M'\,q$, which assigns to an $A_0$-algebra $T$ the set of variable-change classes of Weierstrass curves over $T$ with unit discriminant together with $\Gamma_0$-type kernel generators at the prime powers of $M'$, a level-$\ell$ structure and a Drinfeld $q$-basis. Finally let $x$ be a $K$-point of this problem whose $j$-invariant has image in $L(\!(T)\!)$ equal to $\mathrm{jqNModC}\,L\,(q\ell)$, the $q$-expansion of $j$ in the variable $T^{q\ell}$. Then the set of minimal primes over $(0)$ in $B_0$ is finite, and its cardinality is at most $\ell-1$.
--
--   This is the count of irreducible components of the full-level moduli ring over a base that does not contain $\zeta_q$: the $(\ell-1)(q-1)$ components indexed by the values of the Weil pairings over $A=A_0[\zeta_q]$ descend to at most $\ell-1$ over $A_0$. It is used in the uniqueness statement singling out the minimal prime of $B_0$ attached to the Tate point at level $q\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_finite_minimalPrimes_and_ncard_le_sub_one_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_of_jOf_eq.lean

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

theorem ModularCurve.FullLevel.finite_minimalPrimes_and_ncard_le_sub_one_gamma0Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_of_jOf_eq
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
    [Algebra.FiniteType A₀ P₀.B₀]

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ)) :
    (⊥ : Ideal P₀.B₀).minimalPrimes.Finite ∧ (⊥ : Ideal P₀.B₀).minimalPrimes.ncard ≤ ℓ - 1 := by sorry
