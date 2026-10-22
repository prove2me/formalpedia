-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_primal_feasible
-- name    : NashFlowLT.SteadyState.primal_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:26.965478+00:00
-- url     : https://prove2.me/theorems/fe4afca9-fa4c-473c-b9a7-b31ccb0c2fd5
-- title:
--   Proof of Theorem 3, p. 13 — if $u_0$ is at most every $st$-cut capacity, the min-cost flow program (P) is feasible
-- statement:
--   Let a fluid queuing network satisfy the standing assumptions, and suppose the inflow rate is at most the capacity of every $st$-cut:
--   $$u_0\le\sum_{e\in\delta^+(S)}\nu_e\qquad\text{for every } S\subseteq V \text{ with } s\in S,\ t\notin S .$$
--   Then the program (P) is feasible: there is a static $st$-flow $y'$ of value $u_0$ with $0\le y'_e\le\nu_e$ for every arc $e$.
--
--   This is the step where the hypothesis $u_0\le\bar\nu$ of Theorem 3 enters: feasibility gives (P) a finite optimal value $\alpha$, which bounds the potential.
--
--   **Formalization Note** "$u_0\le\bar\nu$ with $\bar\nu$ the minimal cut capacity" is stated as $u_0$ being at most the capacity of every cut, which avoids defining a minimum. Cuts are given by node sets $S$ and consist of the arcs leaving $S$.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, pp. 12–13, proof of Theorem 3; (P) on p. 10

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proof of Theorem 3, p. 13: if `u0` is at most the capacity of every `st`-cut, the min-cost flow
program (P) is feasible. -/
theorem primal_feasible (N : Network V E) (hN : N.Standing)
    (hcut : ∀ S : Finset V, N.s ∈ S → N.t ∉ S → N.u0 ≤ cutCapacity N S) :
    ∃ y : E → ℝ, IsPrimalFeasible N y := by sorry
end NashFlowLT.SteadyState
