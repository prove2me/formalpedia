-- Prove2me | Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
-- name    : ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/130a66cf-98a4-5531-a1cf-027e7e22efea
-- title:
--   The segment period equals F(γ i)-F(i)
-- statement:
--   Let $N$ be a positive natural number, let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ (the congruence subgroup `CongruenceSubgroup.Gamma0 N` of $\mathrm{SL}_2(\mathbb Z)$), and let $F:\mathfrak H\to\mathbb C$ be a function on the upper half-plane satisfying [`ModularCurve.HasEquivariantPrimitive N f F`](def/ModularCurve_PeriodMapBundled.html#L12), i.e. the conjunction of four clauses: for every $\tau\in\mathfrak H$ the function $F\circ\mathrm{ofComplex}$ has derivative $f(\tau)$ at the point $\tau\in\mathbb C$; $F$ tends to $0$ along the filter `atImInfty`; for every $\gamma\in\Gamma_0(N)$ there is a constant $c\in\mathbb C$ with $F(\gamma\cdot z)-F(z)=c$ for all $z\in\mathfrak H$; and for every $\delta\in\mathrm{SL}_2(\mathbb Z)$ the function $w\mapsto F(\delta\cdot w)$ has a limit $L\in\mathbb C$ along `atImInfty`. Then for every $\gamma\in\Gamma_0(N)$ the value at $f$ of the period functional [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92), namely the functional [`ModularCurve.periodAlong N I (γ • I)`](def/ModularCurve_PeriodLattice.html#L78) defined by integrating `periodIntegrand N I (γ • I) f` over $t\in[0,1]$, equals $F(\gamma\cdot i)-F(i)$, where $i\in\mathfrak H$ is `UpperHalfPlane.I` and $\gamma$ acts through its image in $\mathrm{SL}_2(\mathbb Z)$.
--
--   This identifies the concrete period of a weight-$2$ cusp form along the straight segment from $i$ to $\gamma i$ with the difference of values of an equivariant primitive $F$, so that the homomorphism and limit properties of $F$ transfer to the period functionals spanning the period lattice. It is used throughout the comparison of the Abel–Jacobi map with the period lattice, in particular in the statements about cusp forms whose periods realise prescribed elements of that lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitive N f F) (γ : CongruenceSubgroup.Gamma0 N) :
    ModularCurve.period N γ f =
      F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.I) - F UpperHalfPlane.I := by sorry
