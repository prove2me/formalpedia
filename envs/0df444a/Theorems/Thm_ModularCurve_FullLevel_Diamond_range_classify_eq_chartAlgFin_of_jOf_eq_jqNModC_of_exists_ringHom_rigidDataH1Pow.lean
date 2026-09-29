-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/92d9a6f2-e85c-51f1-9be7-6a133b7ac442
-- title:
--   Range of the H₁-classifying map is the finite chart algebra
-- statement:
--   Let $q$ be a prime, $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell_g$-th root of unity admitting a ring homomorphism $\iota:L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ (the group [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)) with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K$ be the intermediate field of $L\subset L(\!(\mathsf q)\!)$ generated over $L$ by the image, under coefficientwise extension of scalars, of the $q$-expansion function field of level $H_1$ and modulus $q^2M'$ over $\mathbb Q$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in its maximal ideal, acting on $K$ compatibly, and let $j\in K$ be non-zero with Laurent expansion the classical $j$-series. Assume $\ell_g$ and $M'$ are units in $A$; assume the three covariance hypotheses $h\ell$, $hM$, $hL$ expressing that $\Gamma_1(\ell_g)$-points (affine equation, vanishing of $\operatorname{pre}\Psi_{\ell_g}$ at $x_P$, and $(x_Q,y_Q)=(x_P,y_P)$), the $\Gamma_0$-prime-power kernel polynomial conditions, and the divisibility by `inLineMulPoly` are preserved by variable change; let $\mathcal G$ be a family of relative group laws on projective Weierstrass models over $A$-algebras that is chord–tangent and has the origin as identity, and $\mathcal T$ a level transport for $q$ satisfying the section-transport condition; assume finally that variable changes and coefficient maps are realised by graded ring homomorphisms of the projective model rings respecting the irrelevant ideals ($hVC$, $hCO$). Let $D$ be the moduli datum `rigidDataH1Pow` built from these data (Weierstrass curves with unit discriminant carrying a $\Gamma_0$-tuple for $M'$, a $\Gamma_1(\ell_g)$-point, a Drinfeld $q$-basis, and the $\Gamma_1$-link divisibility, modulo variable change), and let $P_0$ be an abstract fine moduli package for $D$, that is an $A$-algebra $B_0$ of finite type with a universal point through which every $D$-point over every $A$-algebra factors uniquely. Then for every $x\in D(K)$ whose $j$-invariant has Laurent expansion the $j$-series with all exponents multiplied by $q$, the range of the classifying $A$-algebra homomorphism $B_0\to K$ attached to $x$ equals `chartAlgFin A K j`, the $A$-subalgebra of elements of $K$ integral over $A[j]$.
--
--   This identifies the finite chart of the two-chart integral model of the modular curve, namely the integral closure of $A[j]$ in $K$, with the image of the fine moduli ring of the $H_1$-level problem ($\Gamma_0(M')\cap\Gamma_1(\ell_g)$ together with Drinfeld $q$-level structure) under evaluation at the Tate-curve point with $j$-invariant $j(\mathsf q^q)$. It is the diamond-edition counterpart of the corresponding statement with auxiliary full $\Gamma(\ell)$-level, imposing no lower bound on $q$, and it is used downstream to realise elements of the chart algebra by moduli-theoretic constructions on Tate curves and to compare level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_rigidDataH1Pow
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
    [Algebra.FiniteType A P₀.B₀] :
    ∀ (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K),
      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q →
      (P₀.classify x).range = AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by sorry
