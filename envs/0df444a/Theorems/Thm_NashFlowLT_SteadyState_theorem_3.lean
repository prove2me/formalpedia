-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_theorem_3
-- name    : NashFlowLT.SteadyState.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:25.213669+00:00
-- url     : https://prove2.me/theorems/71aad935-bed3-4793-aca6-1207910f50bc
-- title:
--   Theorem 3, p. 12 — if $u_0$ is at most every $st$-cut capacity, every dynamic equilibrium reaches a steady state in finite time
-- statement:
--   Let a fluid queuing network satisfy the standing assumptions: capacities $\nu_e>0$, delays $\tau_e\ge 0$, inflow rate $u_0>0$, source $s\neq t$, and every node reachable from $s$. Let $\bar\nu=\min_C\sum_{e\in C}\nu_e$ be the minimal capacity of an $st$-cut. If
--   $$u_0\le\bar\nu,$$
--   then every dynamic equilibrium $(f^+,z)$ attains a steady state in finite time: there is $\theta_0\ge 0$ such that
--   $$z_e(\theta)=z_e(\theta_0)\qquad\text{for every arc } e \text{ and every } \theta\ge\theta_0 .$$
--
--   When the network can carry the inflow, queues stop changing after a finite time, so travel times become constant and the equilibrium settles into the stationary regime described by the min-cost flow program (P) and its dual.
--
--   **Formalization Note** "$u_0\le\bar\nu$" is stated as $u_0\le\sum_{e\in\delta^+(S)}\nu_e$ for every node set $S$ with $s\in S$, $t\notin S$. "The dynamic equilibrium" is read as every dynamic equilibrium, since equilibria need not be unique. The steady state is about the queue lengths $z_e$ in real time, as defined on p. 9. Added to the page: $s\neq t$, reachability of every node from $s$, and local integrability of the inflows (see the model file).
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 12, Theorem 3

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 3, p. 12: if the inflow rate `u0` is at most the capacity of every `st`-cut (i.e. at most
the minimum cut capacity `ν̄`), then every dynamic equilibrium attains a steady state in finite time. -/
theorem theorem_3 (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F)
    (hcut : ∀ S : Finset V, N.s ∈ S → N.t ∉ S → N.u0 ≤ cutCapacity N S) :
    AttainsSteadyState N F := by sorry
end NashFlowLT.SteadyState
