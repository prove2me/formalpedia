-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/2e125c78-7421-5ed5-bdfe-1d3309939366
-- title:
--   Unramified level sets of the modular unit on the Gauss component
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$ and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the image, under coefficientwise application of $\mathbb{Q} \to L$, of the $q$-expansion function field of $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, with a compatible $A$-algebra structure on $K$. Let $j \in K$ be non-zero with $q$-expansion the coefficientwise image of $q^{-1}\,\mathrm{jNumQ}$, and write $\mathcal{O} =$ [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) for the $A$-subalgebra of $K$ of elements integral over $A[j]$. Let $u \in \mathcal{O}$ have $q$-expansion the coefficientwise image of $\Delta(q)/\Delta(q^p)$ ([`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127)). Let $W_0$ be a valuation subring of $K$ characterised by: $f \in W_0$ if and only if there are $x, y \in A[[q]]$ with $y$ non-zero modulo the maximal ideal of $A$ and $f \cdot y = x$ inside $L((q))$; and let $P_0$ be a prime ideal of $\mathcal{O}$ consisting exactly of those $b$ whose image in $K$ lies in the non-units of $W_0$. Then there is a non-zero polynomial $\mathrm{avoid} \in (\mathbb{Z}/p)[X]$ such that for every $h \in \mathbb{Z}[X]$ whose reduction modulo $p$ has positive degree, is separable and is coprime to $\mathrm{avoid}$, the ring $\mathcal{O} / (P_0 + (h(u)))$ is non-trivial and formally unramified over $\mathbb{Z}$.
--
--   This is the statement that, on the $j$-finite chart of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$, the level sets of the modular unit $\Delta(q)/\Delta(q^p)$ along the Gauss (Igusa) component are non-empty and unramified over $\mathbb{Z}$, apart from finitely many critical values encoded by the polynomial $\mathrm{avoid}$. It feeds the corresponding statement for other primes of the chart algebra and the construction of finite étale quotients of the chart algebra used in the study of reduction of $X_1(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (u : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))))
    (P₀ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) [P₀.IsPrime] (hP₀ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ P₀ ↔ (b : ↥K) ∈ W₀.nonunits) :
    ∃ avoid : (ZMod p)[X], avoid ≠ 0 ∧
      ∀ h : ℤ[X], 0 < (h.map (Int.castRingHom (ZMod p))).natDegree → (h.map (Int.castRingHom (ZMod p))).Separable →
        IsCoprime (h.map (Int.castRingHom (ZMod p))) avoid →
        Nontrivial (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₀ ⊔ Ideal.span {Polynomial.aeval u h})) ∧
        Algebra.FormallyUnramified ℤ (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₀ ⊔ Ideal.span {Polynomial.aeval u h})) := by sorry
