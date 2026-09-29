-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/c6b839f4-479f-5a27-ab31-02a0e488a9f2
-- title:
--   Finiteness of modular-unit level quotients on the j-chart
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $M\neq 0$ and $p\nmid M$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta\in L$ be a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L\subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A\to L$, together with an $A$-algebra structure on $K$ compatible with $A\to L\to K$. Let $j\in K$ be the element whose $q$-expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) (the $j$-invariant series $q^{-1}\cdot\,$`jNumQ`), assumed nonzero, and let $\mathcal{O}=$ [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135), the subalgebra of elements of $K$ integral over $A[j]$. Let $v\in\mathcal{O}$ have $q$-expansion either the modular unit series $\Delta(q)\,\Delta(q^{p})^{-1}$ ([`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127)) or $p^{12}$ times its inverse. Then there is $K_b\in\mathbb{N}$ such that for every monic $g\in\mathbb{Z}[X]$ whose reduction modulo $p$ has nonzero constant coefficient, $\mathcal{O}/(g(v))$ is a finite $A$-module with `Module.finrank` over $A$ at most $K_b\cdot\deg g$.
--
--   This is the finiteness-with-linear-degree-bound statement for the level sets of the modular unit $\Delta(\tau)/\Delta(p\tau)$ on the $j$-finite chart of the integral two-chart model of $X_1(Mp)$ over a ramified base $A$; the bound $K_b\deg g$ is uniform in $g$. It feeds the corresponding statement producing finite étale quotients, [`ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (v : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hv : ((v : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∨
      ((v : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    :
    ∃ Kb : ℕ, ∀ g : ℤ[X], g.Monic → (g.map (Int.castRingHom (ZMod p))).coeff 0 ≠ 0 →
      Module.Finite A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
      Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ Kb * g.natDegree := by sorry
