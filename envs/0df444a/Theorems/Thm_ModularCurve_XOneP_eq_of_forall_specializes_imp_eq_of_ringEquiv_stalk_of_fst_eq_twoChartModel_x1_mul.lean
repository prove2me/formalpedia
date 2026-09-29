-- Prove2me | Theorems.Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/557b9b10-3ff8-51d0-af6c-e457c364014e
-- title:
--   Uniqueness of the minimal special-fibre point over a valuation point
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137), i.e. the subfield generated over $L$ by the coefficientwise image of that field of $q$-series. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in $\mathfrak{m}_A$ and $\zeta$ comes from $A$, with an $A$-algebra structure on $K$ compatible with $A\to L\to K$, and let $j\in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. The assertion is: for all points $y,y'$ of the pullback of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) along `specMap A k` (the geometric special fibre over $k$) such that every point specialising to $y$ equals $y$, and likewise for $y'$; for every valuation subring $V$ of $K$ containing the image of $A$, sending $\mathfrak{m}_A$ into the nonunits of $V$, and such that $P(j)$ and $P(j)^{-1}$ lie in $V$ for every polynomial $P$ over $A$ whose reduction modulo $\mathfrak{m}_A$ is nonzero; given that the image $z$ of $y$ under `pullback.fst` lies in the open image of the finite chart [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231), and given a ring isomorphism $\varphi$ from the stalk of [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) at $z$ onto $V$ which carries the germ at $z$ of each element $a$ of [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) (the elements of $K$ integral over $A[j]$) to $a$ itself inside $K$: if $y$ and $y'$ have the same image under `pullback.fst`, then $y=y'$.
--
--   The statement says that the fibre over such a point $z$ of the projection from the geometric special fibre of the two-chart model of $X_1(Mp)$ to the model itself contains at most one minimal point, the hypotheses on $V$ pinning $z$ down as a point whose local ring is a valuation ring of $K$ lying over $A$, over $\mathfrak{m}_A$ and over the generic point of the $j$-line modulo $\mathfrak{m}_A$. It is used in the analysis of the special fibre of this model at $p$ — the branch ideal and Krull dimension of the stalk, and the identification of the two Igusa components through their Gauss readings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k] :
    ∀ (y y' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (_ : ∀ t, t ⤳ y → t = y) (_ : ∀ t, t ⤳ y' → t = y')
      (V : ValuationSubring ↥K)
      (_ : ∀ a : A, algebraMap A ↥K a ∈ V)
      (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits)
      (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
      (hz : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
      (φ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) ≃+* ↥V)
      (_ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((φ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V) : ↥K) = (a : ↥K)),
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y =
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y' → y = y' := by sorry
