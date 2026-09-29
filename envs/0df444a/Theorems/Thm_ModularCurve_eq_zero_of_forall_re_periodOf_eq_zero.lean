-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
-- name    : ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/c0a3c859-bbcf-5f52-8a95-ae640a008ab5
-- title:
--   Real periods detect vanishing of weight-2 cusp forms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index and let $f$ be a cusp form of weight $2$ on $\Gamma$, in the sense of Mathlib's `CuspForm Γ 2`. For each $\gamma \in \Gamma$ the functional [`ModularCurve.periodOf Γ γ`](def/ModularCurve_PeriodOf.html#L56) is the $\mathbb{C}$-linear functional on `CuspForm Γ 2` obtained as [`ModularCurve.periodAlongOf Γ`](def/ModularCurve_PeriodOf.html#L42) at the pair of points $i$ and $\gamma \cdot i$ of the upper half-plane, namely the functional sending a weight-2 cusp form $g$ to $\int_0^1 \mathtt{periodIntegrandOf}\,\Gamma\,i\,(\gamma\cdot i)\,g\,t \, \mathrm{d}t$, the integral over the unit parameter interval of the integrand attached to the path from $i$ to $\gamma \cdot i$; linearity in the form is part of that definition. The hypothesis is that for every $\gamma \in \Gamma$ the complex number [`ModularCurve.periodOf Γ γ f`](def/ModularCurve_PeriodOf.html#L56) has real part $0$. The conclusion is that $f = 0$ in `CuspForm Γ 2`.
--
--   This is the injectivity half of the Eichler–Shimura correspondence over $\mathbb{R}$: the real-linear map sending a weight-2 cusp form to the real parts of its periods $\int_i^{\gamma i} f$ along $\Gamma$ is injective, which is what makes the period lattice span the real dual of $S_2(\Gamma)$. It is used in the construction of the Eichler–Shimura map into the first cohomology of modular curves for groups $\Gamma_H$, and thence in the comparison of cusp forms with Galois representations and Hecke modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 := by sorry
