-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/84dbeae8-7986-583e-b6ea-ab880a8bd61d
-- title:
--   Reduced special fibre at an ordinary point, H₁ level
-- statement:
--   Let $A$ be a discrete valuation ring which is a domain, $q$ a prime, $M'\ge 1$ with $q\nmid M'$, and $\ell_g$ a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$; assume $q$ lies in the maximal ideal of $A$ while $\ell_g$ and $M'$ are units in $A$. Assume the transport hypotheses for the $H_1$ level data: stability of [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) under variable change, stability of [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) under `kernelVariableChangeDeg`, and stability of divisibility of `inLineMulPoly` under variable change; a family $\mathcal G$ of relative group laws on the projective models of Weierstrass curves with unit discriminant over $A$-algebras which is chord–tangent (compatible with addition and Galois twisting on points over fields) and has the identity section given by the origin chart with $x/y, z/y\mapsto 0$; a transport $\mathcal T$ of raw Drinfeld pairs preserving Drinfeld $\Gamma(q)$-bases, satisfying the section-transport compatibilities; and the existence of graded variable-change and coefficient homomorphisms between projective model rings dominating the irrelevant ideals. Let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataH1Pow` (a ring $B_0$ with universal point and unique classification of points of $A$-algebras) with $B_0$ of finite type over $A$, let $\mathfrak p$ be a minimal prime of $B_0$, and suppose the residue field of $A$ is finite. Let $\varpi$ generate the maximal ideal of $A$, $\varepsilon$ a unit with $\varpi^{q-1}=\varepsilon q$, and $\zeta$ a primitive $q$-th root of unity in $A$. Let $xr$ be a raw datum over $B_0$ — a Weierstrass curve with unit discriminant, $\Gamma_0(M')$-kernel polynomials, a $\Gamma_1(\ell_g)$-point linked to them, and a Drinfeld pair — whose class is the universal point, let $x$ be a maximal ideal of $B_0/\mathfrak p$ containing the image of the maximal ideal of $A$, and let $F_0$ be a formal group over $(B_0/\mathfrak p)/x$ whose power series is the fixed formal group law of the reduction of $xr.\mathrm{curve}$, with $F_0$ ordinary in the sense that its $q$-th iterate series equals a unit times $X^q$. Then the residue field of $A$ tensored over $A$ with the $x$-adic completion of $B_0/\mathfrak p$ is reduced.
--
--   This is the statement that the special fibre of the completed local ring of a component of the $H_1=\Gamma_0(M')\cap\Gamma_1(\ell_g)$ fine moduli ring at an ordinary point is reduced, in the style of Katz–Mazur's analysis of the fibres of modular curves of full level $q$. It feeds the reducedness statement at an arbitrary minimal prime, used in the local study of the modular curve of level $q$ along the Diamond route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_rigidDataH1Pow.lean

import Mathlib
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
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_rigidDataH1Pow
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)

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
    [Algebra.FiniteType A P₀.B₀]    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes)
    [Finite (IsLocalRing.ResidueField A)] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (xr : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hxr : (Quot.mk _ xr : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (x : Ideal (P₀.B₀ ⧸ 𝔭)) [x.IsMaximal]
    (hxA : (IsLocalRing.maximalIdeal A).map (algebraMap A (P₀.B₀ ⧸ 𝔭)) ≤ x)
    (F₀ : FormalGroup ((P₀.B₀ ⧸ 𝔭) ⧸ x))
    (hF₀W : F₀.toPowerSeries = ((xr.curve.map (Ideal.Quotient.mk 𝔭)).map (Ideal.Quotient.mk x)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries ((P₀.B₀ ⧸ 𝔭) ⧸ x), IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q) :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A) (AdicCompletion x (P₀.B₀ ⧸ 𝔭))) := by sorry
