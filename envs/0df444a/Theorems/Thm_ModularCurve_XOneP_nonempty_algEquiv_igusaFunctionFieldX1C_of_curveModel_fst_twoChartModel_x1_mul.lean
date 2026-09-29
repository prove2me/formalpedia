-- Prove2me | Theorems.Thm_ModularCurve_XOneP_nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_fst_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_fst_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/7a056d7b-d065-5144-b02b-dcc982b3a76e
-- title:
--   Function field of the first special-fibre component is Igusa's
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$. Let $L$ be a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, let $\zeta \in L$ be a primitive $p$-th root of unity, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image of the function field $\mathrm{x1FunctionField}(Mp) \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ under coefficientwise extension along $\mathbb{Q} \to L$. Let $A$ be a discrete valuation ring with fraction field $L$ whose maximal ideal contains $p$ and whose image contains $\zeta$, with $K$ an $A$-algebra compatibly with $L$, and let $j \in K$, $j \neq 0$, have Laurent expansion the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra, and write $X_k$ for the pullback of the two-chart model $\mathrm{modelTo}\,A\,K\,j$ along $\operatorname{Spec} k \to \operatorname{Spec} A$. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, let $i_1, i_2$ be closed immersions of $C_1, C_2$ into $X_k$ over $\operatorname{Spec} k$ (i.e. $i_\nu$ followed by the structure map of $X_k$ is $c_\nu$), assume every point of $X_k$ lies in the image of $i_1$ or of $i_2$, that the scheme-theoretic pullback of $i_1$ and $i_2$ is reduced and has exactly $n$ points with $n > 0$; let $\varepsilon$ be a section of the two-chart model over $\operatorname{Spec} A$, let $\varepsilon_1, \varepsilon_2$ be sections of $c_1, c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$ to $k$. Finally let $w$ be an integral weight-one form over $k$ of level $M$: a weight-one modular form on $\Gamma_1(M)$ together with a power series over $\mathbb{Z}$ which is its $q$-expansion and whose image in $k$ has nonzero constant datum `intSeriesC`. Then for every field $F$ that is a $k$-algebra, every curve model of $F$ over $k$ (an integral scheme with a proper smooth relative-dimension-one morphism to $\operatorname{Spec} k$, a ring isomorphism of $F$ with its function field over $k$, a bijection between its closed points and the places of $F$ over $k$ matching stalks with valuation subrings, and such that every finite set of points lies in an affine open), and every isomorphism $e$ of that model's curve with $C_1$ over $\operatorname{Spec} k$ (i.e. $e$ followed by $c_1$ is the model's structure morphism), $F$ is isomorphic as a $k$-algebra to the Igusa function field $\mathrm{igusaFunctionFieldX1C}\,k\,M\,w \subseteq \mathrm{LaurentSeries}\,k$, namely the Igusa extension of $\mathrm{x1FunctionFieldC}\,k\,M$ attached to the Hasse-root function of $w$.
--
--   This is the function-field half of the statement that the components of the geometric special fibre at $p$ of the model of $X_1(Mp)$ are Igusa curves: the component singled out by the section $\varepsilon_1$ lying under $\varepsilon$ has function field the Igusa field $\mathrm{Ig}(M;p)$ over $k$. Quantifying over all curve models $(F, \mathcal{M}, e)$ of $C_1$ transports the conclusion to any chosen function field; the result is used in the construction of such a model identification, [`ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_fst_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_fst_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_fst_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.nonempty_algEquiv_igusaFunctionFieldX1C_of_curveModel_fst_twoChartModel_x1_mul
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
    ∀ (F : Type) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C₁),
      e.hom ≫ c₁ = Mdl.toBase → Nonempty (F ≃ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := by sorry
