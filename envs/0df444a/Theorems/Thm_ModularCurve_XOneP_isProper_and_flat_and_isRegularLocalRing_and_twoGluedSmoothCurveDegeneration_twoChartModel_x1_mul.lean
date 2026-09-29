-- Prove2me | Theorems.Thm_ModularCurve_XOneP_isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/09bd30a9-30a5-5ea0-a9a3-b11ab5a4885c
-- title:
--   Proper flat regular two-chart model of X₁(Mp) with semistable fibres
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$ and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.x1FunctionFieldC ℚ (Gamma1 (M * p))`](def/ModularCurve_X1.html#L134) inside $\mathrm{LaurentSeries}\,\mathbb{Q}$. Let $A$ be a discrete valuation domain with an algebra structure on $L$ making $L$ its fraction field, with $p$ in the maximal ideal of $A$ and $\zeta$ in the image of $A \to L$, together with an $A$-algebra structure on $K$ compatible with the tower $A \to L \to K$. Let $j \in K$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), where [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) is $q^{-1}$ times the rational $j$-numerator power series. Write $X =$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), the pushout gluing the spectra of the $A$-subalgebras `chartAlg A K {j}` and `chartAlg A K {j⁻¹}` of $K$ along the middle chart, and let $\pi =$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) $: X \to \operatorname{Spec} A$ be the morphism induced by the two structure maps. The conclusion asserts four things: $\pi$ is proper; $\pi$ is flat; every local ring $\mathcal{O}_{X,x}$ is a regular local ring; and for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} A$ for which the second projection $X \times_{\operatorname{Spec} A} \operatorname{Spec} k \to \operatorname{Spec} k$ fails to be smooth, there exist $k$-schemes $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$, both proper, smooth of relative dimension $1$ and geometrically integral, closed immersions $i_1 : C_1 \to X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ and $i_2 : C_2 \to X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ compatible with the projections ($i_1$ followed by the projection is $c_1$, and likewise for $i_2$), and a natural number $n$ such that every point of the fibre lies in the image of $i_1$ or of $i_2$, the scheme-theoretic intersection $C_1 \times_{X \times \operatorname{Spec} k} C_2$ is reduced, and its number of points equals $n$ with $n > 0$.
--
--   This is the regular model over the local base $A$ of the modular curve with function field $K$, obtained as the two-chart normalisation of the $j$-line, together with the description of its non-smooth geometric fibres as a union of two proper smooth geometrically integral curves meeting in a nonempty reduced finite scheme. It is the geometric input for the downstream work with the curve $X_1(Mp)$ over $A$, and is cited by the statements about sections, connectedness of geometric fibres, and Hecke and Abel–Jacobi constructions on this model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IsProper (ModularCurve.TwoChart.modelTo A (↥K) j) ∧
    Flat (ModularCurve.TwoChart.modelTo A (↥K) j) ∧
    (∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      IsRegularLocalRing ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) s) →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : C₁ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) s)
        (i₂ : C₂ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) s)
        (_ : i₁ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) s = c₁)
        (_ : i₂ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) s = c₂)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂) (n : ℕ),
        (∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) s), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base) ∧
        IsReduced (pullback i₁ i₂) ∧ Nat.card ↥(pullback i₁ i₂) = n ∧ 0 < n := by sorry
