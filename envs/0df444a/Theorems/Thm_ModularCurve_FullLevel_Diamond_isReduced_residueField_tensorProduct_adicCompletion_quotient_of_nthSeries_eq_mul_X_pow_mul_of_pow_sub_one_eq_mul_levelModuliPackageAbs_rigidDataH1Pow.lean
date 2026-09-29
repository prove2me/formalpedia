-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_mul_of_pow_sub_one_eq_mul_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_mul_of_pow_sub_one_eq_mul_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/7c659ddf-f209-533b-98ee-dd2a06130b72
-- title:
--   Reduced special fibre at a supersingular point, H₁ level
-- statement:
--   Let $A$ be a discrete valuation domain, $q$ a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell_g$ a prime with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$; assume $q \in \mathfrak m_A$ while $\ell_g$ and $M'$ are units in $A$. Three transport hypotheses are assumed for all $A$-algebras $T$: the $\Gamma_1(\ell_g)$-point condition (a point $(x_P,y_P)$ on the curve, repeated in the $Q$-slot, with $\Psi_{\ell_g}$-numerator vanishing at $x_P$) is preserved by variable change, the condition `IsGamma0PowAt` on a kernel polynomial is preserved by `kernelVariableChangeDeg`, and divisibility of `inLineMulPoly` is likewise preserved. Further data: group laws $\mathcal G$ on projective Weierstrass models which are chord–tangent and have the origin as identity, a level transport $\mathcal T$ for Drinfeld bases of level $q$ satisfying `IsSectionTransport`, and the two hypotheses `hVC`, `hCO` providing graded homomorphisms of projective-model rings realising variable changes and coefficient maps compatibly with irrelevant ideals. Let $P_0$ be a fine moduli package, with universal ring $B_0$ of finite type over $A$, for the moduli datum attached to `rigidDataH1Pow`, whose points over $T$ are Weierstrass curves with unit discriminant equipped with a tuple of `IsGamma0PowAt` kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell_g)$-point, a Drinfeld basis of level $q$, and the link that the $\ell_g$-component kernel polynomial divides `inLineMulPoly` at $x_P$, modulo variable change. Let $\mathfrak p$ be a minimal prime of $B_0$; assume the residue field of $A$ is finite, $\mathfrak m_A = (\varpi)$ with $\varpi^{q-1} = \varepsilon q$ for a unit $\varepsilon$, and $A$ contains a primitive $q$-th root of unity $\zeta$. Let $xr$ be a raw point over $B_0$ whose class is the universal point, let $x$ be a maximal ideal of $B_0/\mathfrak p$ containing the image of $\mathfrak m_A$, and let $F_0$ be a formal group over $(B_0/\mathfrak p)/x$ whose power series is the fixed formal group law of the reduction of $xr$'s curve and whose $q$-th iterated sum series `nthSeries q` equals a unit times $X^{q\cdot q}$. Then the ring $\kappa(A) \otimes_A \widehat{(B_0/\mathfrak p)}_x$ is reduced.
--
--   This is the Katz–Mazur statement that, at a supersingular point of a component of the fine moduli ring for the $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell_g)$ Drinfeld-level problem, the special fibre of the completed local ring is reduced. It feeds the corresponding assertion for an arbitrary minimal prime of the universal ring, on the way to regularity and reducedness statements for these moduli rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_mul_of_pow_sub_one_eq_mul_levelModuliPackageAbs_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

open scoped MatrixGroups TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_mul_of_pow_sub_one_eq_mul_levelModuliPackageAbs_rigidDataH1Pow
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
    [Algebra.FiniteType A P₀.B₀]
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes)

    [Finite (IsLocalRing.ResidueField A)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))

    (ζ : A) (hζ : IsPrimitiveRoot ζ q)

    (xr : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hxr : (Quot.mk _ xr : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (x : Ideal (P₀.B₀ ⧸ 𝔭)) [x.IsMaximal]
    (hxA : (IsLocalRing.maximalIdeal A).map (algebraMap A (P₀.B₀ ⧸ 𝔭)) ≤ x)

    (F₀ : FormalGroup ((P₀.B₀ ⧸ 𝔭) ⧸ x))
    (hF₀W : F₀.toPowerSeries =
      ((xr.curve.map (Ideal.Quotient.mk 𝔭)).map (Ideal.Quotient.mk x)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries ((P₀.B₀ ⧸ 𝔭) ⧸ x), IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ (q * q)) :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A) (AdicCompletion x (P₀.B₀ ⧸ 𝔭))) := by sorry
