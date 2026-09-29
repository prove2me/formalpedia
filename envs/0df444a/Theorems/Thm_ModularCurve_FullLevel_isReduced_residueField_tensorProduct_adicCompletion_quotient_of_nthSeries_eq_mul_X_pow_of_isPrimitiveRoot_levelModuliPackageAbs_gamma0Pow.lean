-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/95b5312e-93e8-54fe-a33e-e1d2fd45e5e1
-- title:
--   Reduced special fibre at an ordinary point
-- statement:
--   Let $A$ be a discrete valuation domain, $q\ge 5$ and $\ell\ge 3$ primes with $\ell\neq q$, and $M'\neq 0$ with $q\nmid M'$; assume $q\in\mathfrak m_A$ while $\ell$ and $M'$ are units in $A$. Fix: equivariance of level-$\ell$ structures and of $\Gamma_0$-type kernel polynomials under Weierstrass variable changes (`hℓ`, `hM`); a family $\mathcal G$ of relative group laws on the projective models that is chord–tangent and has the origin as identity; a transport $\mathcal T$ of Drinfeld pairs compatible with the sections (`h𝒯`); and the existence of graded homomorphisms realising variable changes and coefficient changes (`hVC`, `hCO`). Let $P_0$ be a fine moduli package for the rigidified datum $\Gamma_0(M')\times\Gamma(\ell)\times\text{Drinfeld-}\Gamma(q)$, i.e. an $A$-algebra $B_0$ of finite type with a universal point representing the functor, and let $\mathfrak p$ be a minimal prime of $B_0$. Assume the residue field of $A$ is finite, $\mathfrak m_A=(\varpi)$, $\varpi^{q-1}=\varepsilon q$ with $\varepsilon$ a unit, and $\zeta\in A$ a primitive $q$-th root of unity. Let $xr$ be a raw point (curve with unit discriminant plus level data) representing the universal point, $x$ a maximal ideal of $B_0/\mathfrak p$ containing the image of $\mathfrak m_A$, and $F_0$ a formal group over $(B_0/\mathfrak p)/x$ equal to the formal group law of the reduction of $xr$'s curve, whose $q$-th series is $u\,X^{q}$ for a unit $u$. Then $\kappa(A)\otimes_A \widehat{(B_0/\mathfrak p)}_x$ is reduced.
--
--   This is the ordinary case of the multiplicity-one statement for the components of the full-level moduli ring (Katz–Mazur 13.7.6): at a point of the special fibre where the universal formal group has height one, the completed local ring of each irreducible component has reduced special fibre. It feeds the local-to-global reducedness statement [`ModularCurve.FullLevel.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow`](thm.html#ModularCurve.FullLevel.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.isReduced_residueField_tensorProduct_adicCompletion_quotient_of_nthSeries_eq_mul_X_pow_of_isPrimitiveRoot_levelModuliPackageAbs_gamma0Pow
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)

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
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes)
    [Finite (IsLocalRing.ResidueField A)] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (xr : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hxr : (Quot.mk _ xr : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (x : Ideal (P₀.B₀ ⧸ 𝔭)) [x.IsMaximal]
    (hxA : (IsLocalRing.maximalIdeal A).map (algebraMap A (P₀.B₀ ⧸ 𝔭)) ≤ x)
    (F₀ : FormalGroup ((P₀.B₀ ⧸ 𝔭) ⧸ x))
    (hF₀W : F₀.toPowerSeries = ((xr.curve.map (Ideal.Quotient.mk 𝔭)).map (Ideal.Quotient.mk x)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries ((P₀.B₀ ⧸ 𝔭) ⧸ x), IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q) :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A) (AdicCompletion x (P₀.B₀ ⧸ 𝔭))) := by sorry
