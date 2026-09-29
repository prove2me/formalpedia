-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isReduced_levelModuliPackageAbs_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/b3e0e101-2a6d-527d-a2be-0a094a05c61c
-- title:
--   Reducedness of the H₁-level fine moduli ring over A₀
-- statement:
--   Fix a prime $q$, a natural number $M'$ with $M'\neq 0$ and $q\nmid M'$, and a prime $\ell$ with $\ell\equiv 11 \pmod{12}$ and $\ell\mid M'$. On the analytic side one is given a field $L$ of characteristic zero, a primitive $(q\ell)$-th root of unity $\xi\in L$ admitting a ring embedding $\iota\colon L\to\mathbb{C}$ with $\iota\xi=e^{2\pi i/(q\ell)}$, the subgroup $H_1\le(\mathbb{Z}/q^2M')^\times$ cut out as the intersection of the kernels of the reductions to $(\mathbb{Z}/q)^\times$ and to $(\mathbb{Z}/\ell)^\times$, the intermediate field $K$ of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $\mathbb{Q}$-function field `xHFunctionField` of level $(q^2M',H_1)$, a discrete valuation ring $A$ with fraction field $L$ such that $q$ lies in its maximal ideal, with $K$ an $A$-algebra compatibly with $L$, and a nonzero $j\in K$ whose underlying Laurent series is the coefficientwise image of the $q$-expansion `jq`. Over this sits a discrete valuation ring $A_0$ with maximal ideal $(q)$, mapping to $A$ and to $K$ compatibly, with $A$ finite over $A_0$, an element $\zeta_A\in A$ whose image in $L$ is a primitive $q$-th root of unity and which generates $A$ as an $A_0$-algebra, a primitive $\ell$-th root of unity in $A_0$, and units $\ell,M'$ in $A_0$. Further data: the equivariance of the level conditions under variable change, namely that `IsGamma1Point` for $\ell$ (the point $(x_P,y_P)$ lies on the affine curve, $\operatorname{pre}\Psi_\ell$ vanishes at $x_P$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved, that `IsGamma0PowAt` is preserved under `kernelVariableChangeDeg`, and that divisibility of `inLineMulPoly` is preserved; a family $\mathcal{G}$ of relative group laws on the Proj models of Weierstrass curves with unit discriminant over $A_0$-algebras, chord–tangent on points over fields and with identity section the origin chart section; a transport $\mathcal{T}$ of raw Drinfeld pairs of level $q$ along algebra maps and variable changes, preserving the Drinfeld-basis condition and compatible with the induced maps of Proj models; and the existence, for every variable change and every coefficient change, of graded ring homomorphisms of the Proj-model gradings realising them and satisfying the irrelevant-ideal condition. Finally, $P_0$ is a representing object for the moduli datum attached to `rigidDataH1Pow` $A_0\,\ell\,M'\,q$ — an $A_0$-algebra $P_0.B_0$ of finite type with a universal point, unique up to unique $A_0$-algebra map — and $x$ is a point of that datum over $K$ whose $j$-invariant is, as a Laurent series, `jqNModC` $L\,q$. The conclusion is that the ring $P_0.B_0$ is reduced.
--
--   This is the reducedness half of the standard passage from a fine moduli ring over a discrete valuation ring to its geometric properties: flatness over $A_0$ plus reducedness of the generic fibre. It feeds the companion statement that the same ring is a domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isReduced_levelModuliPackageAbs_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd.lean

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
attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_rigidDataH1Pow_of_maximalIdeal_eq_span_of_adjoin_eq_top_tatePoint_of_isPrimitiveRoot_mul_of_dvd
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
    [Algebra.FiniteType A₀ P₀.B₀]

    (x : (rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q)

    : IsReduced P₀.B₀ := by sorry
