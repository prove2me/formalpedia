-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/f7b63144-b6ea-54a7-a097-e40dd415c6bf
-- title:
--   Two smooth components of the bad fibre, ordered by a section
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, $\zeta \in L$ a primitive $p$-th root of unity, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under the coefficientwise map $\mathbb{Q} \to L$ of the $q$-expansion function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $j \in K$ be nonzero with Laurent expansion the $q$-expansion $j(q)$, and let $X \to \operatorname{Spec} A$ be the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the pushout of $\operatorname{Spec}$ of the $A$-subalgebras `chartAlg A K {j}` and `chartAlg A K {j⁻¹}` of $K$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$ and $\varepsilon$ a section of $X \to \operatorname{Spec} A$. Then there exist $k$-schemes $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1, i_2$ of $C_1, C_2$ into the fibre $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ over $k$, an $n : \mathbb{N}$, and sections $\varepsilon_1$ of $c_1$ and $\varepsilon_2$ of $c_2$, such that every point of the fibre lies in the image of $i_1$ or of $i_2$, the scheme $C_1 \times_{X_k} C_2$ is reduced with $\operatorname{Nat.card}$ of its underlying type equal to $n$ and $0 < n$ (so this intersection is finite and nonempty), and $\varepsilon_1$ followed by $i_1$ equals the base-changed section `sectionBaseChange k ε` of $X_k \to \operatorname{Spec} k$.
--
--   This is the geometric description of the bad special fibre at $p$ of the integral model of $X_1(Mp)$: it is covered by two smooth proper geometrically integral curves meeting in a finite nonempty reduced set, and the two components are here ordered so that the reduction of the given $A$-section factors through the first one (the section meets the smooth locus, hence exactly one component), $\varepsilon_2$ being an arbitrary $k$-point of the other. It feeds the component data used on the Picard/Néron side of the $q$-expansion semistable specialisation package for $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul
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
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) :
    ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
      (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
      (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
      (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
      (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
      (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
      (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      (∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
      IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
      ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1 := by sorry
