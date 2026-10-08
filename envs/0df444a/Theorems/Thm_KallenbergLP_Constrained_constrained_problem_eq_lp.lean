-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_constrained_problem_eq_lp
-- name    : KallenbergLP.Constrained.constrained_problem_eq_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:10.849995+00:00
-- url     : https://prove2.me/theorems/2f8b7c33-c31a-4e72-b3d5-c2bcc94ff00c
-- title:
--   Theorem 4.7.3 — the constrained problem (4.7.5) and the linear program (4.7.6) are equivalent
-- statement:
--   Let $\beta$ be an initial distribution, $q_{iak}$ and $b_k$ ($k=1,\dots,m$) the data of the additional constraints, and consider the constrained Markov decision problem (4.7.5), $\sup_{R\in C_1}\{\phi(\beta,R)\mid\sum_i\sum_aq_{iak}x_{ia}(R)\le b_k\}$, and the linear program (4.7.6), $\max\sum_i\sum_ar_{ia}x_{ia}$ subject to (4.7.7) and $\sum_i\sum_aq_{iak}x_{ia}\le b_k$. Then:
--
--   1. Problem (4.7.5) is feasible if and only if problem (4.7.6) is feasible.
--   2. The optima of the problems (4.7.5) and (4.7.6) are equal.
--   3. If $R$ is an optimal solution of (4.7.5), then $x(R)$ is an optimal solution of (4.7.6).
--   4. Let $(x,y)$ be an optimal solution of (4.7.6) and write $x=\sum_kp_kx(f_k)$ with $p_k\ge0$, $\sum_kp_k=1$, where $f_1,\dots,f_n$ are all the pure stationary policies and $x(f)$ is given by (4.7.2). If $R$ is a Markov policy with
--
--   $$\sum_i\beta_i\,\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i)=\sum_i\beta_i\sum_kp_k\,\mathbb P_{f_k^\infty}(X_t=j,\ Y_t=a\mid X_1=i)\qquad(t\in\mathbb N,\ a\in A(j),\ j\in E),$$
--
--   then $R$ is an optimal solution of (4.7.5).
--
--   The theorem reduces the constrained average-reward problem to one linear program and shows how to read off an optimal Markov policy from its solution.
--
--   **Formalization Note** The optima are compared in the extended reals, so part 2 also covers the infeasible case (both $-\infty$). In part 4 the book's $R$ is the Markov policy of Theorem 2.5.1 (Derman–Strauch) satisfying (4.7.11); the Lean statement asserts optimality for every Markov policy satisfying (4.7.11).
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 140–141, Theorem 4.7.3, (4.7.11)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies
import Definitions.Def_KallenbergLP_Constrained_Problem

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.3, pp. 140–141: the constrained Markov decision problem (4.7.5)
and the linear program (4.7.6) are equivalent: (i) equal feasibility, (ii) equal optima,
(iii) an optimal policy gives an optimal `x(R)`, (iv) a Markov policy `R` reproducing the
mixture (4.7.11) of pure stationary policies is optimal. -/
theorem constrained_problem_eq_lp {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) {m : ℕ} (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ) (b : Fin m → ℝ) :
    ((∃ R, Feasible475 β q b R) ↔ (∃ x y, Feasible476 M β q b x y)) ∧
    value475 β q b = value476 M β q b ∧
    (∀ R, Optimal475 β q b R → ∀ x ∈ limitPoints β R, ∃ y, Optimal476 M β q b x y) ∧
    (∀ x y, Optimal476 M β q b x y →
      ∀ pk : PureRule M → ℝ, (∀ f, 0 ≤ pk f) → ∑ f, pk f = 1 →
      x = ∑ f, pk f • xStat β (pureWeights f) →
      ∀ R : AvgHRPolicy M, IsMarkov R →
      (∀ (t : ℕ) (p : KallenbergLP.AverageLP.Pair M), ∑ i, β i * prob R t i p =
          ∑ i, β i * ∑ f, pk f * prob (pureStationaryPolicy f) t i p) →
      Optimal475 β q b R) := by sorry

end KallenbergLP.Constrained
