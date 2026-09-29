-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/ac82678a-7a1f-5619-ab86-7a3b055bbae0
-- title:
--   Unramified level sets of p¹²/u on the far branch
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, and let $L$ be a field of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$, with $\zeta\in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$, let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal and $\zeta$ is in the image of $A$, with $A$ acting on $K$ compatibly, and let $j\in K$, assumed nonzero, have $q$-expansion $q^{-1}\cdot(\text{numerator series of }j)$. Write $\mathcal{O}$ for the algebra of elements of $K$ integral over $A[j]$. Let $u,u'\in\mathcal{O}$ have $q$-expansions $\Delta(q)/\Delta(q^p)$ and $p^{12}\bigl(\Delta(q)/\Delta(q^p)\bigr)^{-1}$ respectively. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ with $fy=x$ for some $x,y\in A[[q]]$ with $y$ nonzero modulo the maximal ideal, let $\sigma$ be an $L$-algebra automorphism of $K$ with $\sigma u=u'$ which preserves membership in $\mathcal{O}$ in both directions, let $W_1=\sigma^{-1}W_0$, and let $P_1$ be a prime of $\mathcal{O}$ cut out by the nonunits of $W_1$. Then there is a nonzero $\mathrm{avoid}\in\mathbb{F}_p[X]$ such that for every $h\in\mathbb{Z}[X]$ whose reduction mod $p$ has positive degree, is separable and is coprime to $\mathrm{avoid}$, the quotient $\mathcal{O}/(P_1+(h(u')))$ is nontrivial and formally unramified over $\mathbb{Z}$.
--
--   This is the $u'$-leg of the unramifiedness statement for level sets of the modular unit $\Delta(q)/\Delta(q^p)$ on the $j$-finite chart over $A=\mathbb{Z}_p[\zeta_p]$: the same conclusion as for the Gauss prime $P_0$, but on the second branch $W_1=\sigma^{-1}W_0$ of the special fibre of $X_1(Mp)$, whose centre is $P_1$. It feeds the construction of finite étale quotients of the chart algebra used further on in the Frey-curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Polynomial

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (hu' : ((u' : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))))

    (σ : ↥K ≃ₐ[L] ↥K) (hσu : σ (u : ↥K) = (u' : ↥K))
    (hσ𝒪 : ∀ b : ↥K, b ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j ↔ σ b ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j)
    (W₁ : ValuationSubring ↥K) (hW₁ : ∀ f : ↥K, f ∈ W₁ ↔ σ f ∈ W₀)
    (P₁ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) [P₁.IsPrime] (hP₁ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ P₁ ↔ (b : ↥K) ∈ W₁.nonunits)
    :
    ∃ avoid : (ZMod p)[X], avoid ≠ 0 ∧
      ∀ h : ℤ[X], 0 < (h.map (Int.castRingHom (ZMod p))).natDegree → (h.map (Int.castRingHom (ZMod p))).Separable →
        IsCoprime (h.map (Int.castRingHom (ZMod p))) avoid →
        Nontrivial (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₁ ⊔ Ideal.span {Polynomial.aeval u' h})) ∧
        Algebra.FormallyUnramified ℤ (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₁ ⊔ Ideal.span {Polynomial.aeval u' h})) := by sorry
