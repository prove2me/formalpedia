-- Prove2me | Theorems.Thm_ModularCurve_periodAlong_smul_sub_periodAlong_eq_period
-- name    : ModularCurve.periodAlong_smul_sub_periodAlong_eq_period
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/4f700048-0e9e-5a67-997a-3bc40e63726c
-- title:
--   Segment periods along a Γ₀(N)-orbit differ by a period
-- statement:
--   Let $N$ be a positive integer, let $\gamma$ be an element of the congruence subgroup $\Gamma_0(N) \subset \mathrm{SL}_2(\mathbb{Z})$, and let $\tau$ be a point of the upper half-plane $\mathbb{H}$. For points $\tau_0, \tau_1 \in \mathbb{H}$, the functional $\mathtt{periodAlong}\ N\ \tau_0\ \tau_1$ is the element of the $\mathbb{C}$-linear dual of the space of weight-two cusp forms for $\Gamma_0(N)$ that sends $f$ to the interval integral $\int_0^1 f(\tau_0 + \mathrm{clamp}_{[0,1]}(t)(\tau_1 - \tau_0))\,(\tau_1 - \tau_0)\,dt$, i.e. the integral of $f(z)\,dz$ along the straight segment from $\tau_0$ to $\tau_1$; and $\mathtt{period}\ N\ \gamma$ is by definition $\mathtt{periodAlong}\ N\ i\ (\gamma \cdot i)$, the segment integral from $i$ to $\gamma \cdot i$. The assertion is an identity of linear functionals on the space of weight-two cusp forms for $\Gamma_0(N)$: the segment period from $i$ to $\gamma \cdot \tau$ minus the segment period from $i$ to $\tau$ equals the period attached to $\gamma$. Equivalently, for every weight-two cusp form $f$ on $\Gamma_0(N)$, $\int_i^{\gamma\tau} f(z)\,dz - \int_i^{\tau} f(z)\,dz = \int_i^{\gamma i} f(z)\,dz$, all integrals being taken along segments.
--
--   This is the statement that translating a point by $\Gamma_0(N)$ changes the segment integral $\int_i^{\tau} f(z)\,dz$ only by the lattice period attached to the translating matrix, so that the Abel–Jacobi map of a divisor on $\mathbb{H}$ is well defined modulo the period lattice on $\Gamma_0(N) \backslash \mathbb{H}$. It is used in the construction of the Abel–Jacobi map and in the statements that fibre sums and untwisted multipliers lie in, or converge into, the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodAlong_smul_sub_periodAlong_eq_period.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlong_smul_sub_periodAlong_eq_period
    (N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ModularCurve.periodAlong N UpperHalfPlane.I ((γ : SL(2, ℤ)) • τ) -
      ModularCurve.periodAlong N UpperHalfPlane.I τ = ModularCurve.period N γ := by sorry
