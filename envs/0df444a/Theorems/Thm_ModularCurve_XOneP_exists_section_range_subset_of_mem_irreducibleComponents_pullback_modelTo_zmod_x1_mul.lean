-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_section_range_subset_of_mem_irreducibleComponents_pullback_modelTo_zmod_x1_mul
-- name    : ModularCurve.XOneP.exists_section_range_subset_of_mem_irreducibleComponents_pullback_modelTo_zmod_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/b4f368fb-477f-5156-9a72-0435e385001a
-- title:
--   An 𝔽ₚ-section on every component of the mod p fibre
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (the map on Laurent series induced by $\mathbb{Q} \to L$) of the $q$-expansion function field [`ModularCurve.x1FunctionFieldC ℚ`](def/ModularCurve_X1.html#L134) of $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A \to L$, equipped with an algebra structure on $K$ compatible with $A \to L \to K$, and with an $A$-algebra structure on $\mathbb{Z}/p$. Let $j \in K$ be an element, nonzero as a `Fact`, whose Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Then for every irreducible component $Z$ of the underlying space of the fibre product of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) (the structure morphism to $\operatorname{Spec} A$ of the two-chart model, obtained by descending the two chart structure maps along the pushout) with $\operatorname{Spec}(\mathbb{Z}/p) \to \operatorname{Spec} A$, there exists a morphism $x \colon \operatorname{Spec}(\mathbb{Z}/p) \to$ this fibre product which is a section of the second projection and whose topological image is contained in $Z$.
--
--   This is the statement that every irreducible component of the special fibre at $p$ of the two-chart model of $X_1(Mp)$ over $A$ carries an $\mathbb{F}_p$-rational point, provided by the reductions of cusps. It is used in the identification of the components of that special fibre with curves over $\mathbb{Z}/p$ as a pullback, in [`ModularCurve.XOneP.exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_section_range_subset_of_mem_irreducibleComponents_pullback_modelTo_zmod_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_section_range_subset_of_mem_irreducibleComponents_pullback_modelTo_zmod_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [Algebra A (ZMod p)] :
    ∀ Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))),
      ∃ x : Spec (CommRingCat.of (ZMod p)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)),
        x ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = 𝟙 _ ∧ Set.range x.base ⊆ Z := by sorry
