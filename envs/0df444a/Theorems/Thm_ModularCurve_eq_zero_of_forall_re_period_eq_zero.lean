-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_forall_re_period_eq_zero
-- name    : ModularCurve.eq_zero_of_forall_re_period_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/f7495764-0c60-5da5-8725-55ecc8dfc884
-- title:
--   Vanishing of all real periods forces f=0
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N)$, i.e. an element of `CuspForm (CongruenceSubgroup.Gamma0 N) 2`. For each $\gamma \in \Gamma_0(N)$ the functional [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92) is the $\mathbb{C}$-linear functional on weight-$2$ cusp forms given by [`ModularCurve.periodAlong N`](def/ModularCurve_PeriodLattice.html#L78) at the pair of points $i \in \mathbb{H}$ and $\gamma \cdot i$, where $\gamma$ acts through its image in $\mathrm{SL}_2(\mathbb{Z})$; here `periodAlong N τ₀ τ₁` sends a cusp form $g$ to the interval integral $\int_0^1 \mathtt{periodIntegrand } N\, \tau_0\, \tau_1\, g\, t \, \mathrm{d}t$ of the integrand [`ModularCurve.periodIntegrand`](def/ModularCurve_PeriodLattice.html#L56) parametrising the period of $g$ from $\tau_0$ to $\tau_1$, and is $\mathbb{C}$-linear in $g$ by additivity and homogeneity of that integrand together with integrability. The hypothesis is that for every $\gamma \in \Gamma_0(N)$ the complex number [`ModularCurve.period N γ f`](def/ModularCurve_PeriodLattice.html#L92) has real part zero, that is, all the periods $\int_i^{\gamma i} f$ are purely imaginary. The conclusion is that $f = 0$ in the space of weight-$2$ cusp forms for $\Gamma_0(N)$.
--
--   This is the injectivity half of the real Eichler–Shimura map $S_2(\Gamma_0(N)) \to H^1(\Gamma_0(N), \mathbb{R})$, $f \mapsto (\gamma \mapsto \operatorname{Re} \int_i^{\gamma i} f)$; equivalently, the period lattice of $\Gamma_0(N)$ spans the $\mathbb{R}$-dual of $S_2(\Gamma_0(N))$. It underlies the period-lattice and Abel–Jacobi statements of the complex-place dictionary for modular curves, and is proved from the existence of an equivariant primitive [`ModularCurve.exists_hasEquivariantPrimitive`](thm.html#ModularCurve.exists_hasEquivariantPrimitive) together with the expression of periods as differences of such a primitive, [`ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive`](thm.html#ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_forall_re_period_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eq_zero_of_forall_re_period_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) : f = 0 := by sorry
