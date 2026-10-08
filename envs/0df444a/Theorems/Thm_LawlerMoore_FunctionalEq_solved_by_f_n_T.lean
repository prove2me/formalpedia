-- Prove2me | Theorems.Thm_LawlerMoore_FunctionalEq_solved_by_f_n_T
-- name    : LawlerMoore.FunctionalEq.solved_by_f_n_T
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:53.369279+00:00
-- url     : https://prove2.me/theorems/7689967c-8053-46ee-97f1-99d24fc18411
-- title:
--   Section 1 — for nondecreasing losses, f(n, T) with T = Σ max{a_j, b_j} is the minimum total loss
-- statement:
--   Consider $n$ jobs performed one at a time in the fixed order $1, \dots, n$. Job $j$ takes $a_j$ time units and incurs loss $\alpha_j(t)$ if completed at time $t$ in the first mode, or $b_j$ units and loss $\beta_j(t)$ in the other. Let $f$ be defined by Eq. (1). Suppose every $\alpha_j$ and every $\beta_j$ is monotone nondecreasing, and put
--   $$T = \sum_{j=1}^{n} \max\{a_j, b_j\}.$$
--   Then $f(n, T)$ solves the problem "what assignment of modes to jobs and what timing of the jobs will minimize the total loss?":
--   1. $f(n, T)$ is finite;
--   2. $f(n, T) \le L(m, c)$ for every mode assignment $m$ and every feasible timing $c$ of all $n$ jobs (no deadline, idle time allowed);
--   3. some mode assignment and feasible timing attain $L(m, c) = f(n, T)$.
--
--   This is the paper's justification that the whole problem is solved by one table of (1), of size $n \times T$.
--
--   **Formalization Note** "The problem is solved by the calculation of $f(n, T)$" is read as items 1–3: $f(n,T)$ is the attained minimum total loss over all timings, with no bound on the completion times. Monotone nondecreasing is `Monotone` on the natural-number completion time. The hypothesis is needed: one job with $a = b = 1$, $\alpha(1) = 5$, $\alpha(t) = 0$ for $t \ge 2$ and $\beta \equiv 5$ has optimum $0$ at $c = 2 > T = 1$.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 77, Section 1 (after Eq. (1))

import Mathlib
import Definitions.Def_LawlerMoore_FunctionalEq_Problem
import Definitions.Def_LawlerMoore_FunctionalEq_Recursion

namespace LawlerMoore.FunctionalEq

/-- Section 1, p. 77 (after Eq. (1)): if every loss function `α_j`, `β_j` is monotone
nondecreasing in the completion time, then the problem is solved by `f(n, T)` with
`T = ∑_{j=1}^n max {a_j, b_j}`: `f(n, T)` is finite, it is at most the total loss of every
mode assignment with every feasible timing of all `n` jobs (no deadline), and some mode
assignment with some feasible timing attains it. -/
theorem solved_by_f_n_T {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ)
    (hα : ∀ j, Monotone (α j)) (hβ : ∀ j, Monotone (β j)) :
    f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) ≠ ⊤ ∧
      (∀ (m : Fin n → Bool) (c : Fin n → ℕ), IsFeasible a b m c n →
        f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) ≤ ((totalLoss α β m c n : ℝ) : WithTop ℝ)) ∧
      ∃ (m : Fin n → Bool) (c : Fin n → ℕ), IsFeasible a b m c n ∧
        ((totalLoss α β m c n : ℝ) : WithTop ℝ) = f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) := by sorry

end LawlerMoore.FunctionalEq
