-- Prove2me | Theorems.Thm_LogicBenders_Generic_theorem_1
-- name    : LogicBenders.Generic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:23.545018+00:00
-- url     : https://prove2.me/theorems/b927c8fb-95ea-48fc-887f-3ea29f177a2f
-- title:
--   Theorem 1, p. 9 — with valid cuts (B1), a terminated generic Benders run ends optimal with value z̄, infeasible, or unbounded
-- statement:
--   Consider problem (6), $\min f(x,y)$ subject to $(x,y)\in S$, $x\in D_x$, $y\in D_y$, with $f$ real-valued, and a run of the generic Benders algorithm (Figure 1): start from $\bar z = -\infty$ and an initial $\bar y\in D_y$; while the subproblem dual (8) at $\bar y$ has a feasible solution $\beta > \bar z$, formulate a bounding function $\beta_{\bar y}$ with $\beta_{\bar y}(\bar y) = \beta$ and add the Benders cut $z \ge \beta_{\bar y}(y)$ to the master problem (9); if the master is infeasible, stop; otherwise let $(\bar z,\bar y)$ be an optimal solution of the master with optimal value $\bar z$, and repeat.
--
--   Suppose that in each iteration the bounding function satisfies
--
--   **(B1)** the Benders cut $z \ge \beta_{\bar y}(y)$ is valid: every feasible solution $(x,y)$ of (6) satisfies $f(x,y) \ge \beta_{\bar y}(y)$.
--
--   Then:
--
--   1. If the algorithm terminates with a finite optimal solution $(z,y) = (\bar z,\bar y)$ of the master problem, then (6) has an optimal solution $(x,y) = (\bar x,\bar y)$ with value $f(\bar x,\bar y) = \bar z$:
--   $$(\bar x,\bar y)\in S,\qquad f(\bar x,\bar y) = \bar z,\qquad f(\bar x,\bar y)\le f(x,y)\ \text{ for all } (x,y)\in S.$$
--   2. If it terminates with an infeasible master problem, then (6) is infeasible: $S = \varnothing$.
--   3. If it terminates with an infeasible subproblem dual, then (6) is unbounded: for every real $M$ some $(x,y)\in S$ has $f(x,y) < M$.
--
--   Theorem 1 is the correctness theorem of logic-based Benders decomposition: whatever inference method produces the cuts, validity of the cuts alone guarantees that the algorithm's three ways of stopping report the right answer.
--
--   **Formalization Note.** Iterations are numbered from $0$; a run through $N$ iterations starts with $\bar z_0 = -\infty$ and, at each iteration $k < N$, passes the While test, adds a cut equal to $\beta_k$ at $\bar y_k$, and takes $(\bar z_{k+1},\bar y_{k+1})$ as a master optimum for exactly the cuts $0,\dots,k$. Each clause assumes (B1) for exactly the cuts its run has added: cuts $0,\dots,N-1$ in clauses 1 and 3, cuts $0,\dots,N$ in clause 2. "Finite" is $\bar z_N \neq -\infty$ (the master value is $< +\infty$ by definition of a master optimum). "Infeasible subproblem dual" means no real $\beta$ is dual-feasible. Clause 1 carries one hypothesis not printed in the theorem: **if the optimal value of the subproblem (7) at the terminal $\bar y$ is finite, it is attained**. The proof on p. 9 asserts exactly this ("the subproblem primal (7) has optimal value $\beta^*$ and some optimal solution $\bar x$"), and without it clause 1 is false: with $D_x = \mathbb R$, $D_y$ a single point, $S = \{x > 0\}$, $f(x,y) = x$ and the valid cut $0$, the run stops with $\bar z = 0$ and (6) has no optimal solution. The hypothesis holds automatically when $D_x$ is finite.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 9, Theorem 1 and Figure 1

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem theorem_1 {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (N : ℕ) :
    -- (i) termination with a finite optimal solution `(z̄, ȳ)` of the master problem
    (StopsAtWhile S f r N →
      (∀ k < N, ValidCut S f (r.cut k)) →
      r.zbar N ≠ ⊥ →
      -- attainment of the subproblem (7) at the terminal `ȳ` when its value is finite
      -- (asserted in the proof on p. 9: "some optimal solution x̄")
      (subVal S f (r.ybar N) ≠ ⊤ → subVal S f (r.ybar N) ≠ ⊥ →
        ∃ x : X, (x, r.ybar N) ∈ S ∧ (f x (r.ybar N) : EReal) = subVal S f (r.ybar N)) →
      ∃ xbar : X, (xbar, r.ybar N) ∈ S ∧ (f xbar (r.ybar N) : EReal) = r.zbar N ∧
        ∀ (x : X) (y : Y), (x, y) ∈ S → f xbar (r.ybar N) ≤ f x y) ∧
    -- (ii) termination with an infeasible master problem
    (StopsAtMaster S f r N →
      (∀ k ≤ N, ValidCut S f (r.cut k)) →
      S = ∅) ∧
    -- (iii) termination with an infeasible subproblem dual
    (StopsAtWhile S f r N →
      (∀ k < N, ValidCut S f (r.cut k)) →
      (¬ ∃ β : ℝ, IsDualFeasible S f (r.ybar N) (β : EReal)) →
      IsUnbounded S f) := by sorry

end LogicBenders.Generic
