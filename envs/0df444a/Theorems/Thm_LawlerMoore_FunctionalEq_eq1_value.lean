-- Prove2me | Theorems.Thm_LawlerMoore_FunctionalEq_eq1_value
-- name    : LawlerMoore.FunctionalEq.eq1_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:59:27.035267+00:00
-- url     : https://prove2.me/theorems/c334c1ac-548c-474e-ae82-5ea1ed382947
-- title:
--   Eq. (1) — f(j, t) is the minimum total loss of the first j jobs with job j completed by time t
-- statement:
--   Consider $n$ jobs performed one at a time in the fixed order $1, \dots, n$, job $j$ taking $a_j$ time units with loss $\alpha_j(t)$ at completion time $t$ in one mode, or $b_j$ time units with loss $\beta_j(t)$ in the other. Let $f$ be defined by Eq. (1), and for $0 \le j \le n$ and an integer $t$ let $\mathcal L(j, t)$ be the set of total losses of the first $j$ jobs over all mode assignments and all feasible timings (start at time $0$ or later, one job at a time, idle time allowed) in which job $j$ is completed no later than time $t$.
--
--   Then $f(j, t)$ is the minimum of $\mathcal L(j, t)$:
--   1. $f(j, t) = +\infty$ if and only if $\mathcal L(j, t) = \emptyset$;
--   2. if $f(j, t)$ is a real number $x$, then $x \in \mathcal L(j, t)$ and $x \le L$ for every $L \in \mathcal L(j, t)$:
--   $$f(j, t) = \min\,\mathcal L(j, t).$$
--
--   No assumption is made on the loss functions. This is the content of the paper's sentence defining $f(j, t)$ as a minimum total loss together with the claim that (1) follows "by the usual dynamic programming argumentation".
--
--   **Formalization Note** "Minimum" is read as an attained least element (`IsLeast`), with $+\infty$ exactly when the feasible set is empty. Jobs are 0-based in Lean; times are natural numbers, $t$ an integer.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 77, Eq. (1)

import Mathlib
import Definitions.Def_LawlerMoore_FunctionalEq_Problem
import Definitions.Def_LawlerMoore_FunctionalEq_Recursion

namespace LawlerMoore.FunctionalEq

/-- Eq. (1) (p. 77): for every `j ≤ n` and every integer `t`, the value `f(j, t)` given by the
recursion (1) is the minimum total loss of the first `j` jobs, over all mode assignments and
all feasible timings (idle time allowed, start at time `0`) in which job `j` is completed no
later than time `t`: it is `+∞` exactly when no such timing exists, and otherwise it is a
real number that is attained and is at most every such total loss. No assumption is made on
the losses `α`, `β`. -/
theorem eq1_value {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (hj : j ≤ n)
    (t : ℤ) :
    (f a b α β j t = ⊤ ↔ lossesBy a b α β j t = ∅) ∧
      ∀ x : ℝ, f a b α β j t = (x : WithTop ℝ) → IsLeast (lossesBy a b α β j t) x := by sorry

end LawlerMoore.FunctionalEq
