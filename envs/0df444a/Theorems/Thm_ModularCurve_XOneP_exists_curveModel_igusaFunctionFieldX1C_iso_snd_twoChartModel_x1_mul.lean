-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/6881c9d5-bd33-5aa7-9cb7-dd2529697780
-- title:
--   Second special fibre component of X₁(Mp) is Igusa
-- statement:
--   Fix a prime $p$ and $M$ with $5\le M$ and $p\nmid M$; a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb Q$, with $\zeta\in L$ a primitive $p$-th root of unity; and an intermediate field $K$ of $L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the coefficientwise images of the function field of $X_1(Mp)$ read in $q$-expansions. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be a nonzero element whose $q$-expansion is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81). Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and let $X$ denote the base change to $k$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec}A$, i.e. the second projection of the pullback along $\operatorname{Spec}k\to\operatorname{Spec}A$. Let $c_1:C_1\to\operatorname{Spec}k$ and $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension one and geometrically integral, and let $i_1,i_2$ be closed immersions of $C_1,C_2$ into $X$ compatible with the structure morphisms, whose images together cover the underlying space of $X$, with $C_1\times_X C_2$ reduced and of cardinality $n>0$. Let $\varepsilon$ be a section of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec}A$ and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$. Finally let $w$ consist of a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose reduction `intSeriesC k` is nonzero. Then there exist a curve model over $k$ of the intermediate field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) of $k((q))$ — an integral scheme $\mathrm{Mdl}.C$, proper and smooth of relative dimension one over $k$, with a ring isomorphism of that field onto its function field extending $k$, a bijection of its closed points with the places of the field over $k$ matching local rings with valuation subrings, and every finite set of points contained in an affine open — and an isomorphism $e:\mathrm{Mdl}.C\cong C_2$ over $k$, in the sense that $e$ followed by $c_2$ is the structure morphism of the model.
--
--   This identifies the second of the two components of the geometric special fibre at $p$ of the two-chart model of $X_1(Mp)$ with the smooth proper model of the Igusa function field attached to a weight-one form of level $M$, in the sense of Igusa curves as in Katz–Mazur and Edixhoven. It is one of the two conjuncts of the full statement about both components, and is used in the analysis of the special fibre and in the comparison of the Gauss-reading models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul
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
    ∃ (Mdl : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e : Mdl.C ≅ C₂), e.hom ≫ c₂ = Mdl.toBase := by sorry
