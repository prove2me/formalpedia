-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_isClosedImmersion_pair_specialFibre_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.exists_isClosedImmersion_pair_specialFibre_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/c2635fca-7215-514b-b4f0-0365c7d964af
-- title:
--   Geometric special fibre of the two-chart model: two components
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of the Laurent series field $L((q))$ generated over $L$ by the image, under coefficientwise application of $\mathbb{Q} \to L$, of the $\mathbb{Q}$-rational $q$-expansion function field of $X_1(Mp)$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, together with an $A$-algebra structure on $K$ compatible with that of $L$. Let $j \in K$ be nonzero with image in $L((q))$ the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the $j$-invariant, and let $k$ be an algebraically closed field of characteristic $p$ with an $A$-algebra structure. Write $X \to \operatorname{Spec} A$ for the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) with its structure morphism [`AlgebraicCurve.TwoChartIntegralModel.toBase`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258), namely the scheme obtained as the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions of the $A$-subalgebras `chartAlg A ↥K {j}` and `chartAlg A ↥K {j⁻¹}` of $K$ into the middle chart ring, mapping to $\operatorname{Spec} A$ by the two chart structure maps. Then there exist $0$-universe schemes $C_1, C_2$ with morphisms $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, together with morphisms $i_1 : C_1 \to X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ and $i_2 : C_2 \to X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ (pullback of `toBase` along $\operatorname{Spec}$ of $A \to k$) such that $i_1$ followed by the projection to $\operatorname{Spec} k$ is $c_1$ and likewise for $i_2$, both $i_1$ and $i_2$ are closed immersions, every point of the geometric special fibre lies in the image of $i_1$ or of $i_2$ on underlying topological spaces, and neither image is contained in the other.
--
--   This records that the geometric special fibre at $p$ of the two-chart integral model of $X(\Gamma_1(M) \cap \Gamma_1(p))$ over a discrete valuation ring with $\zeta_p$ is covered by two distinct proper smooth geometrically integral curves over $k$ (Igusa-type components), in the manner of Katz–Mazur and Edixhoven. It supplies the component data used by [`ModularCurve.XOneP.exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_components_specialFibre_card_pos_and_section_comp_eq_twoChartModel_x1_mul) and by the regular-model statement [`ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_isClosedImmersion_pair_specialFibre_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.exists_isClosedImmersion_pair_specialFibre_twoChartIntegralModel_x1_mul
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
    ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
      (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
      (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
      (i₁ : C₁ ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A k))))
      (i₂ : C₂ ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A k))))
      (_ : i₁ ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) _ = c₁)
      (_ : i₂ ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) _ = c₂)
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂),
      (∀ z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A k)))),
        z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base) ∧
      ¬ (Set.range i₁.base ⊆ Set.range i₂.base) ∧ ¬ (Set.range i₂.base ⊆ Set.range i₁.base) := by sorry
