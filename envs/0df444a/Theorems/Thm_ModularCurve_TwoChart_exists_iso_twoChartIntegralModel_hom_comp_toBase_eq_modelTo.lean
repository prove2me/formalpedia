-- Prove2me | Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
-- name    : ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/74bf758f-3aea-5ea5-b38f-e43ca5205e78
-- title:
--   The two two-chart models of the j-line agree over Spec A
-- statement:
--   Let $A$ be a commutative ring, $K$ a field equipped with an $A$-algebra structure, and $j \in K$ with $j \neq 0$. Both [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) and [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) are defined as the pushout, in the category of schemes, of the two morphisms $\mathrm{Spec}$ of the middle chart algebra $\to \mathrm{Spec}$ of `chartAlg A K {j}` and $\mathrm{Spec}$ of the middle chart algebra $\to \mathrm{Spec}$ of `chartAlg A K {j⁻¹}` obtained by applying $\mathrm{Spec}$ to the algebra inclusions `inclFin` and `inclInf`; here `chartAlg A K S` denotes the $A$-subalgebra of $K$ attached to a subset $S$ by the project's construction, and the structure morphisms [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) and [`AlgebraicCurve.TwoChartIntegralModel.toBase A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) to $\mathrm{Spec} A$ are in each case the morphism out of the pushout determined by $\mathrm{Spec}$ of the structure maps $A \to$ `chartAlgFin` and $A \to$ `chartAlgInf`. The assertion is that there exists an isomorphism of schemes $e$ from [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) to [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) such that $e$ followed by `toBase` equals `modelTo`, and such that each of the two chart morphisms `ιFin`, `ιInf` into the first pushout, followed by $e$, equals the corresponding chart morphism into the second.
--
--   This is a compatibility statement between two parallel presentations of the same two-chart ($j$ and $1/j$) integral model of a rational curve over $\mathrm{Spec} A$: one recorded in the modular-curve vocabulary, the other in the curve-theoretic vocabulary. It serves as a bridge allowing sections, fibres, closed immersions into fibres and relative Picard data stated over one model to be transported to the other, and is cited by the statements concerning the special fibre and cusp sections of the level-$p$ modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)] :
    ∃ e : ModularCurve.TwoChartModel A K j ≅ AlgebraicCurve.TwoChartIntegralModel A K j,
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A K j = ModularCurve.TwoChart.modelTo A K j ∧
      ModularCurve.TwoChart.ιFin A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin A K j ∧
      ModularCurve.TwoChart.ιInf A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf A K j := by sorry
