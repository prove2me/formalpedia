-- Prove2me | Theorems.Thm_ModularCurve_XOneP_sectionBaseChange_not_mem_range_of_comp_eq_sectionBaseChange_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.sectionBaseChange_not_mem_range_of_comp_eq_sectionBaseChange_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/5dd8a7f9-5cd4-5b74-b84a-2d6ae265b08a
-- title:
--   Section through one special-fibre component misses the other
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image, under the coefficientwise map $L((q)) \leftarrow \mathbb{Q}((q))$ induced by $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) attached to $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with an $A$-algebra structure on $K$ compatible with the tower $A \to L \to K$, and let $j \in K$ be nonzero with image in $L((q))$ the coefficientwise image of $q^{-1}\,\mathrm{jNumQ}(q)$. The two-chart model $X = \mathrm{Spec}\,A[j] \cup \mathrm{Spec}\,A[j^{-1}]$, formed as the pushout of the two affine charts, with its structure morphism $X \to \mathrm{Spec}\,A$, is assumed proper. Let $k$ be an algebraically closed field of characteristic $p$ with an $A$-algebra structure, and write $X_k = X \times_{\mathrm{Spec}\,A} \mathrm{Spec}\,k$ with its projection to $\mathrm{Spec}\,k$. Let $c_1 : C_1 \to \mathrm{Spec}\,k$ and $c_2 : C_2 \to \mathrm{Spec}\,k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ into $X_k$ commuting with the projections to $\mathrm{Spec}\,k$, such that every point of $X_k$ lies in the image of $i_1$ or of $i_2$, the scheme $C_1 \times_{X_k} C_2$ is reduced, and its number of points equals some $n > 0$. Finally let $\varepsilon$ be a section of $X \to \mathrm{Spec}\,A$, let $\varepsilon_1$ be a section of $c_1$, and assume that $\varepsilon_1$ followed by $i_1$ equals the base-changed section $\varepsilon_k : \mathrm{Spec}\,k \to X_k$ obtained from $\varepsilon$. Then for every point $t$ of $\mathrm{Spec}\,k$, the image $\varepsilon_k(t)$ does not lie in the image of $i_2$ on underlying topological spaces.
--
--   This is the geometric separation step for the two-component geometric special fibre of the regular model of $X_1(Mp)$ over the $p$-adic cyclotomic base: a section of the model whose reduction factors through one of the two smooth proper components avoids the other component entirely, so in particular it avoids the crossing locus. It is used in the construction of semistable specialisation data for the $q$-expansion family of $X_1$-curves, where $\varepsilon$ is a cusp and the component through which it reduces is the Igusa component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_sectionBaseChange_not_mem_range_of_comp_eq_sectionBaseChange_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.sectionBaseChange_not_mem_range_of_comp_eq_sectionBaseChange_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1) :
    ∀ t, ((sectionBaseChange k ε).1).base t ∉ Set.range i₂.1.base := by sorry
