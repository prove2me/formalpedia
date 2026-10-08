-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_lp_optimality_correspondence
-- name    : KallenbergLP.OptTransient.lp_optimality_correspondence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:09.452006+00:00
-- url     : https://prove2.me/theorems/d08076ec-2b13-454f-bf1a-92e332cf2ac7
-- title:
--   Theorem 3.3.6 — the policy–LP correspondence preserves optimality
-- statement:
--   Consider a finite substochastic Markov decision model with state space $E$, action sets $A(i)$, transition numbers $p_{iaj}\ge 0$ with $\sum_j p_{iaj}\le 1$ and rewards $r_{ia}$, and fix positive weights $\beta_j>0$, $j\in E$. A transient policy $R^*$ is *optimal transient* if $v_i(R)\le v_i(R^*)$ for every transient policy $R$ (history-dependent and randomized policies included) and every initial state $i$. For a stationary decision rule $\pi$ write $x(\pi)$ for the vector (3.3.11),
--   $$
--   x_{ia}(\pi)=\big[\beta^{\mathsf T}(I-P(\pi))^{-1}\big]_i\,\pi_{ia},
--   $$
--   and for a feasible solution $x$ of the linear program (3.3.7) write $\pi(x)$ for the stationary rule $\pi_{ia}(x)=x_{ia}/\sum_{b} x_{ib}$ of (3.3.8). Then:
--
--   1. if the stationary policy $\pi^\infty$ is an optimal transient policy, then $x(\pi)$ is an optimal solution of the linear program (3.3.7);
--   2. if $x$ is an optimal solution of (3.3.7), then the stationary policy $\pi^\infty(x)$ is an optimal transient policy.
--
--   Together with the one-to-one correspondence of Theorem 3.3.3, this says that optimal stationary transient policies and optimal solutions of (3.3.7) are the same objects.
--
--   **Formalization Note** Optimality of the linear program means feasibility for the equality constraints of (3.3.7) together with a largest objective value among feasible points. No finiteness assumption on the value vector $w$ is made: each part's hypothesis provides it.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 58, Theorem 3.3.6; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.6, printed p. 58: the correspondence of Theorem 3.3.3 preserves optimality. -/
theorem lp_optimality_correspondence {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i) :
    (∀ π : StationaryRule n α, IsStationaryRule m π →
      IsOptimalTransient m (stationaryPolicy π) →
      IsOptimalLP m β (stationaryOccupation m β π)) ∧
    (∀ x : StateAction m → ℝ, IsOptimalLP m β x →
      IsOptimalTransient m (stationaryPolicy (ruleOfOccupation m x))) := by sorry

end KallenbergLP.OptTransient
