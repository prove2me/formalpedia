-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_lemma_10
-- name    : IncrKnapsack.PTAS.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:18.12069+00:00
-- url     : https://prove2.me/theorems/3bba5b5d-d9d0-4831-b0a8-6f67f6da32d0
-- title:
--   Lemma 10, p. 27 — the glued solution S̄ respects every capacity: w(S̄_t) ≤ W_t
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, let $\xi \in \{0,\dots,K-1\}$, and work with the rounded profits of §2.2. Let $\Phi$ be any finite set of grid values, and let $\mathcal A$ be a single-cluster subroutine with the guarantee of Theorem 3. Take any traceback $(m, \tilde\ell_m, \tilde\varphi_m)_{m=0}^M$ of the approximate program $\tilde F$ from the state $(M, L, \tilde\varphi_M)$, where $\tilde\varphi_M$ is the largest grid value with $\tilde F(M, L, \tilde\varphi_M) < \infty$. Let $\bar{\mathcal S}$ be the solution obtained by gluing the single-cluster solutions $\tilde{\mathcal S}^m$ generated along it. Then
--
--   $$w(\bar S_t) \le W_t \qquad\text{for every } t \in [T].$$
--
--   So the algorithm's output is always a feasible solution of the incremental knapsack instance.
--
--   **Formalization Note.** The traceback may pick any minimizer at each step (the paper leaves the choice open); the statement holds for every such choice. Below a terminal state with $\tilde\ell_m = -1$ the states are $(m-1, -1, 0)$. The paper's label $\tilde\ell_0 = -1$ is not imposed: at $m = 1$ every $\ell_0$ gives $\tilde F(0, \ell_0, 0) = 0$, and the proof needs only that the chosen predecessor attains the minimum.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 27–28, §3.6, Lemma 10

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem lemma_10 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    Feasible I (algOut I K ξ Φ A jt ϕt) := by sorry
end IncrKnapsack.PTAS
