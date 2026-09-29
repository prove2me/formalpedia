-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
-- name    : ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e1893a5c-2d29-578c-b99c-240b444a4a4f
-- title:
--   Each bad-fibre component meets every j-level set in one point
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a `DRModelPackage` for $p$ (a Deligne–Rapoport package for the two-chart integral model $\mathrm{DRModel}\,p$ of the full modular curve of level $p$ over $\mathbb Z$, built from the field $\mathrm{modularFunctionFieldFull}\,p$ and its coordinate $\mathrm{IgusaScheme.jFull}\,p$), and let $\kappa$ be an algebraically closed field of characteristic $p$. Let $C$ be a morphism from the scheme $(\mathfrak X.\mathrm{ratModel}\,\kappa).C$ underlying the curve model recorded in the package to the base change $\mathrm{DRModel}\,p \times_{\operatorname{Spec}\mathbb Z} \operatorname{Spec}\kappa$, and assume that $C$ is one of the two component morphisms $\mathfrak X.\mathrm{compInf}\,\kappa$, $\mathfrak X.\mathrm{compZero}\,\kappa$ of the package. The conclusion has two parts. First, for every $c \in \kappa$ there is a closed point $x$ of $(\mathfrak X.\mathrm{ratModel}\,\kappa).C$ such that the complement, inside the topological space of the base change, of the open set $\mathrm{jNeLocus}\,c$ — the union of the basic open set of $j - c$ on the finite-$j$ chart and the basic open set of $1 - c\,j^{-1}$ on the chart at infinity, i.e. the locus $j \neq c$ — meets the image of the continuous map underlying $C$ in exactly the single point $C(x)$. Second, there is a closed point $x$ of $(\mathfrak X.\mathrm{ratModel}\,\kappa).C$ for which the complement of the finite-$j$ chart $\mathrm{chartFinOpenBC}$ (the preimage in the base change of the finite chart), i.e. the locus $j = \infty$, meets the image of $C$ in exactly $C(x)$.
--
--   This is the closed-point, level-set form of the statement that each reduced irreducible component of the fibre of $X_0(p)$ at $p$ maps isomorphically onto the $j$-line under the forgetful map (Deligne–Rapoport V.1; Katz–Mazur 13.4.7): each of the two components of the bad fibre meets each level set $\{j = c\}$, $c \in \kappa \cup \{\infty\}$, in a single point. It is used in the analysis of the crossing points of the two components and in the subsequent construction of affine open covers and germ computations for the Deligne–Rapoport model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (C : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hC : C = 𝔛.compInf κ ∨ C = 𝔛.compZero κ) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ c : κ, ∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) ∧
    (∃ x : closedPoints (𝔛.ratModel κ).C,
      ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range C.base =
        {C.base x.1}) := by sorry
