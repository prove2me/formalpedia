-- Prove2me | Theorems.Thm_ModularCurve_XOneP_nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_snd_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_snd_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/ab0b08a9-a1ca-5458-82eb-d0ce27b4b0e4
-- title:
--   Second component of the special fibre has Igusa function field
-- statement:
--   Fix a prime $p$, an $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ which is a $\{p\}$-cyclotomic extension of $\mathbb Q$ and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image of the $q$-expansion field $\mathbb Q(X_1(Mp))\subseteq\mathbb Q((q))$, let $A$ be a discrete valuation domain with fraction field $L$ whose maximal ideal contains $p$ and whose image contains $\zeta$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$, $j\neq 0$, have image in $L((q))$ the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Assume given proper smooth geometrically integral curves $c_1:C_1\to\operatorname{Spec}k$ and $c_2:C_2\to\operatorname{Spec}k$ of relative dimension $1$, closed immersions $i_1,i_2$ of them over $k$ into the base change to $k$ of the two-chart model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) of $K$ over $A$ in the coordinate $j$, such that every point of that base change lies in the image of $i_1$ or of $i_2$, with $\operatorname{pullback} i_1\,i_2$ reduced and of finite cardinality $n>0$; a section $\varepsilon$ of the two-chart model over $\operatorname{Spec}A$ and sections $\varepsilon_1,\varepsilon_2$ of $c_1,c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base change `sectionBaseChange k ε` of $\varepsilon$; and an integral weight-one form $w$ over $k$ of level $M$, that is, a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose reduction-derived constant `intSeriesC k` is nonzero. The conclusion: for every field $F$ over $k$, every [`AlgebraicCurve.CurveModel k F`](def/AlgebraicCurve_CurveModel.html#L23) (an integral scheme proper and smooth of relative dimension $1$ over $\operatorname{Spec}k$, with an isomorphism of $F$ onto its function field over $k$, a bijection of its closed points with the places of $F/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open) and every isomorphism $e$ of its underlying curve with $C_2$ over $\operatorname{Spec}k$, there exists a $k$-algebra isomorphism $F\simeq$ [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), the Igusa function field inside $k((q))$ attached to $k(X_1(M))$ and the Hasse-root function of $w$.
--
--   This is the function-field half of the statement that the components of the geometric special fibre at $p$ of the model of $X_1(Mp)$ are Igusa curves: the component met by the second closed immersion has function field the Igusa function field of level $M$ over $k$. It is used by [`ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul), which upgrades it to an isomorphism of curves; quantifying over all models $(F,\mathrm{Mdl},e)$ records the $k$-algebra structure carried by [`AlgebraicCurve.CurveModel`](def/AlgebraicCurve_CurveModel.html#L23).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_snd_twoChartModel_x1_mul.lean

import Mathlib
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

theorem ModularCurve.XOneP.nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_snd_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ∀ (F : Type) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C₂),
      e.hom ≫ c₂ = Mdl.toBase → Nonempty (F ≃ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := by sorry
