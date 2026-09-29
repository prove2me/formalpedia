-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus
-- name    : ModularCurve.DRModelPackage.eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/47dc00ed-fc71-54a8-871e-f38ef0bdc9c3
-- title:
--   Uniqueness of the point over 𝒪 on a j-level set
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a `DRModelPackage` for $p$, let $O$ be a commutative ring, let $\kappa$ be an algebraically closed field of characteristic $p$, let $\mathrm{to}\kappa\colon O\to\kappa$ be a ring homomorphism, and let $c\in\kappa$. Write $\mathfrak X_O$ and $\mathfrak X_\kappa$ for the pullbacks of `DRModel.toBase p` (the structure morphism to $\operatorname{Spec}\mathbb Z$ of the two-chart integral model attached to the full modular function field of level $p$ and the element `IgusaScheme.jFull p`) along $\operatorname{Spec}$ of $\mathbb Z\to O$, resp. $\mathbb Z\to\kappa$, and let `DRModel.baseChangeMap toκ` be the induced morphism $\mathfrak X_\kappa\to\mathfrak X_O$ (identity on the model, $\operatorname{Spec}(\mathrm{to}\kappa)$ on the base). Let $J\subseteq\mathfrak X_\kappa$ be the underlying set of the open `TwoChartIntegralModel.jNeLocus ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c`, the join of the basic open of the difference of the $j$-coordinate section and the constant section $c$ on the finite chart with the basic open of $1-c\,j^{-1}$ on the chart at infinity; its complement is the locus $j=c$. Let $x,x'$ be points of $\mathfrak X_O$. Assume: (i) some point $z$ of the scheme $(\mathfrak X.\mathrm{ratModel}\ \kappa).C$ has image $x$ under the map on points of $\mathfrak X.\mathrm{compInf}\ \kappa$ followed by `DRModel.baseChangeMap toκ`, with $(\mathfrak X.\mathrm{compInf}\ \kappa)(z)\notin J$; (ii) the same with $\mathfrak X.\mathrm{compZero}\ \kappa$ in place of $\mathfrak X.\mathrm{compInf}\ \kappa$; (iii) some point $y$ of $\mathfrak X_\kappa$ with $y\notin J$ maps to $x'$ under `DRModel.baseChangeMap toκ`. Then $x'=x$.
--
--   This is the uniqueness statement for points of the Deligne–Rapoport model over $O$ that admit a geometric lift on a fixed level set $j=c$: if one such point is hit by both components of the special fibre on that level set, it is the only one. It is used in the analysis of the crossing points of the model, being cited in the identification of stalks at specialising points and in the computation of the image of a section at a crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (c : κ)
    (x x' : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx₁ : ∃ z : ↥(𝔛.ratModel κ).C, (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base z = x ∧
      (𝔛.compInf κ).base z ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)))
    (hx₂ : ∃ z : ↥(𝔛.ratModel κ).C, (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base z = x ∧
      (𝔛.compZero κ).base z ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)))
    (hx' : ∃ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))), (DRModel.baseChangeMap toκ).base y = x' ∧
      y ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))) :
    x' = x := by sorry
