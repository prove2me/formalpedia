-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/c3048177-e5b0-5d62-bf85-41856ebafb2d
-- title:
--   Reduction of an A-point meets one of two fibre components
-- statement:
--   Fix a prime $p$ and an integer $M \ne 0$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, and let $K$ be an $A$-algebra compatibly with the tower $A \to L \to K$. Let $j \in K$ be nonzero with $j =$ [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) as a Laurent series, and write $X \to \operatorname{Spec} A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the structure morphism of the two-chart model `TwoChartModel A K j`, obtained by gluing the spectra of the $A$-subalgebras `chartAlgFin` and `chartAlgInf` of $K$ attached to $j$ and $j^{-1}$. Let $k$ be an algebraically closed field of characteristic $p$ with an $A$-algebra structure, and let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ into the base change $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$, each compatible with the morphisms to $\operatorname{Spec} k$, and assume that every point of this base change lies in the image of $i_1$ or of $i_2$. Let $\varepsilon$ be a section of $X \to \operatorname{Spec} A$. Then the induced section `sectionBaseChange k ε` of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k \to \operatorname{Spec} k$ factors through $i_1$ or through $i_2$: either there is a section $\varepsilon_1$ of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to it, or there is a section $\varepsilon_2$ of $c_2$ with $\varepsilon_2$ followed by $i_2$ equal to it.
--
--   This is the step saying that the reduction of an $A$-point of the model of $X_1(Mp)$ over a ring containing $\zeta_p$ lies on one of the two given components of the special fibre, so that sections can be sorted by the component they meet. It is used in the statements assembling the components of the special fibre and counting points of the fibre in the two-chart vocabulary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul
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
    {C₁ C₂ : Scheme.{0}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) :
    (∃ ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁, ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1) ∨
    (∃ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂, ε₂.1 ≫ i₂.1 = (sectionBaseChange k ε).1) := by sorry
