-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_gamma0Pow_of_isScalarTower
-- name    : ModularCurve.FullLevel.forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_gamma0Pow_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/5253e233-7f54-5c4a-aebe-465696ae83e0
-- title:
--   Classifying map has image the j-finite chart algebra
-- statement:
--   Fix a prime $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$ and admitting a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, and let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ for the subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$, the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, acting on $K$ compatibly, with $q$ in its maximal ideal, and let $j\in K$, $j\neq 0$, have image in $\mathrm{LaurentSeries}\,L$ the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function pushed to $L$. Let $A_0$ be a discrete valuation domain with maximal ideal $(q)$, containing a primitive $\ell$-th root of unity, acting on $K$ and on $A$ with $A_0\to A\to K$ a scalar tower, and with $\ell$ and $M'$ units in $A_0$. Assume: stability of level-$\ell$ point data ([`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104), four coordinates satisfying the Weierstrass equation, killed by $\mathrm{pre}\Psi_\ell$ and mutually independent) under variable change, and of the $\Gamma_0$-type cyclic-kernel condition [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) under `kernelVariableChangeDeg`; a family $\mathcal{G}$ of relative group laws on the projective models of discriminant-unit Weierstrass curves over $A_0$-algebras, chord–tangent and with origin the identity section; a transport $\mathcal{T}$ of raw Drinfeld pairs of level $q$ which is a section transport; and the existence, for every variable change and every coefficient map of $A_0$-algebras, of a graded ring homomorphism between the projective-model rings realising it, satisfying `IsVariableChangeHom` respectively `IsCoefficientHom` and the stated inequality on irrelevant ideals. Let $P_0$ be a fine moduli package over $A_0$ for the rigidified datum `rigidDataPow` $A_0\,\ell\,M'\,q$, so $P_0.B_0$ is an $A_0$-algebra of finite type carrying a universal point and representing, on $A_0$-algebras, the functor of Weierstrass curves with unit discriminant equipped with $\Gamma_0(p^{v_p(M')})$-kernel polynomials for $p\mid M'$, a level-$\ell$ point pair and a Drinfeld basis of level $q$, modulo variable change. Then for every $K$-point $x$ of this moduli problem whose $j$-invariant has image $\mathrm{jqNModC}\,L\,(q\ell)$ in $\mathrm{LaurentSeries}\,L$, and such that every element of $A$ is a value of the classifying homomorphism $P_0.\mathrm{classify}\,x:P_0.B_0\to K$, the image of that homomorphism is exactly the chart algebra [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) $A\,K\,j$, the $A$-subalgebra of elements of $K$ integral over $A[j]$: every value lies in it, and every one of its elements is a value.
--
--   This identifies the fine moduli ring of the rigidified full-level problem, after evaluation at the Tate-type $K$-point with $j$-invariant the $q$-expansion in the variable $q^{q\ell}$, with the affine $j$-finite chart of the two-chart integral model of the modular curve, in the style of the moduli-theoretic descriptions of Katz–Mazur. It supplies the membership and surjectivity hypotheses of the stalk-comparison results over the supersingular $j$-set which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_gamma0Pow_of_isScalarTower.lean

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

theorem ModularCurve.FullLevel.forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_gamma0Pow_of_isScalarTower
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
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Algebra A₀ ↥K]
    (hω : ∃ ω : A₀, IsPrimitiveRoot ω ℓ)

    [Algebra A₀ A] [IsScalarTower A₀ A ↥K]

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
    [Algebra.FiniteType A₀ P₀.B₀] :
    ∀ (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K),
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) →

      (∀ a : A, ∃ b : P₀.B₀, P₀.classify x b = algebraMap A ↥K a) →
      (∀ b : P₀.B₀, P₀.classify x b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧
      (∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c) := by sorry
