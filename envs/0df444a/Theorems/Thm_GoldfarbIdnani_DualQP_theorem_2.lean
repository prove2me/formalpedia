-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_theorem_2
-- name    : GoldfarbIdnani.DualQP.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:18.53745+00:00
-- url     : https://prove2.me/theorems/35bdb8ba-5ea9-4956-80d1-839cd58a357c
-- title:
--   Theorem 2 — if $n_p = Nr$, either $P(A \cup \{p\})$ is infeasible or dropping a constraint gives a V-triple
-- statement:
--   Let $G$ be symmetric positive definite, let $(x, A)$ be an S-pair for (1.1), and let $p \in K \setminus A$ be a constraint index such that
--
--   $$
--   n^+ \equiv n_p = Nr = \sum_{i \in A} r_i n_i \quad (3.20) \qquad\text{and}\qquad s_p(x) < 0. \quad (3.21)
--   $$
--
--   Let $u = u(x) = N^*g(x)$. Then:
--
--   1. if $r \le 0$, the subproblem $P(A \cup \{p\})$ (minimize $f$ subject to $s_i(x) \ge 0$, $i \in A \cup \{p\}$) has no feasible point;
--   2. otherwise, if $k \in A$ satisfies $r_k > 0$ and
--   $$
--   \frac{u_k}{r_k} = \min_{j \in A,\ r_j > 0} \frac{u_j}{r_j}, \quad (3.22)
--   $$
--   then $(x, A \setminus \{k\}, p)$ is a V-triple.
--
--   The theorem covers the case where the new normal is linearly dependent on the active normals, so that $(x, A, p)$ cannot be a V-triple: either infeasibility is detected, or one constraint is dropped in dual space without moving $x$, after which Theorem 1 applies.
--
--   **Formalization Note.** $r$ is a vector indexed by constraint indices and supported on $A$. "Otherwise" is read as "some $r_j$, $j \in A$, is positive", which is when a minimizing $k$ exists; the statement is given for every such $k$.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 10, Theorem 2, Eqs. (3.20)–(3.22)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

theorem theorem_2 {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (r : Fin m → ℝ)
    (hG : G.PosDef) (hS : IsSPair a G C b x A) (hpA : p ∉ A)
    (hr_supp : ∀ i, i ∉ A → r i = 0)
    (hnp : normal C p = ∑ i ∈ A, r i • normal C i)
    (hp : slack C b x p < 0) :
    ((∀ j ∈ A, r j ≤ 0) → ¬ ∃ y, FeasibleFor C b (insert p A) y) ∧
    (∀ k ∈ A, 0 < r k →
      (∀ j ∈ A, 0 < r j →
        multVec G C A (grad a G x) k / r k ≤ multVec G C A (grad a G x) j / r j) →
      IsVTriple a G C b x (A.erase k) p) := by sorry

end GoldfarbIdnani.DualQP
