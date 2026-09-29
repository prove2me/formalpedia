-- Prove2me | Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
-- name    : ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9f210cd5-40c4-5b4c-94fc-ba0db5fd5d19
-- title:
--   Descent of the parabolic rank bound along a normal subgroup
-- statement:
--   Let $\Gamma'$ and $\Gamma$ be subgroups of $\mathrm{SL}_2(\mathbb Z)$, with $\Gamma'$ of finite index in $\mathrm{SL}_2(\mathbb Z)$, $\Gamma' \le \Gamma$, and $\Gamma'$, viewed as a subgroup of $\Gamma$, normal in $\Gamma$. For a subgroup $\Delta \le \mathrm{SL}_2(\mathbb Z)$ and a commutative coefficient ring, [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) denotes the submodule of those additive homomorphisms from the additive group $\mathrm{Additive}\,\Delta$ to the coefficient module that vanish on every $\gamma \in \Delta$ whose matrix trace satisfies $\mathrm{tr}(\gamma)^2 = 4$, i.e. $\mathrm{tr}(\gamma) = \pm 2$; here it is taken with coefficients $\mathbb Z$, so `parabolicHoms ℤ Δ ℤ` is the group of homomorphisms $\Delta \to \mathbb Z$ killing all elements of trace $\pm 2$. The hypothesis is the inequality $\operatorname{finrank}_{\mathbb Z}\,(\mathtt{parabolicHoms}\ \mathbb Z\ \Gamma'\ \mathbb Z) \le 2\,\dim_{\mathbb C} \mathrm{CuspForm}\,\Gamma'\,2$, where $\mathrm{CuspForm}\,\Delta\,2$ is the space of weight-$2$ cusp forms for $\Delta$. The conclusion is the same inequality with $\Gamma'$ replaced by $\Gamma$: $\operatorname{finrank}_{\mathbb Z}\,(\mathtt{parabolicHoms}\ \mathbb Z\ \Gamma\ \mathbb Z) \le 2\,\dim_{\mathbb C} \mathrm{CuspForm}\,\Gamma\,2$. Finite index is assumed only for $\Gamma'$; that of $\Gamma$ follows from $\Gamma' \le \Gamma$.
--
--   This is the descent step for the surjectivity half of the Eichler–Shimura relation in weight $2$: the bound comparing the rank of the parabolic character group with twice the dimension of the space of cusp forms passes from a finite-index subgroup normal in $\Gamma$ up to $\Gamma$ itself, the mechanism being that the real period map is injective for every finite-index subgroup and equivariant for the action of $\Gamma$ on the data for $\Gamma'$. It is used to deduce the corresponding bound for an arbitrary congruence subgroup, in [`ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup`](thm.html#ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup), from the case of a suitable normal subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
    (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ' ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ' 2)) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by sorry
