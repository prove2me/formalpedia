-- Prove2me | Theorems.Thm_NisanRonen2001_thm5_4_participation_faithful
-- name    : NisanRonen2001.thm5_4_participation_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:01:50.785834+00:00
-- url     : https://prove2.me/theorems/9c10cd09-b8e1-40f4-8f89-c430839d4d17
-- title:
--   Theorem 5.4 — an optimal, strongly truthful mechanism with participation constraints
-- statement:
--   Consider task scheduling with verification: $n \ge 2$ agents and $k$ tasks, agent $i$ needs at least $t^i_j > 0$ time units for task $j$, the mechanism chooses an allocation $x(d)$ from the declarations $d$ and pays each agent $p^i(d, \tilde t)$ after observing the actual times $\tilde t$. A strategy of agent $i$ is a declaration together with an execution plan, and its utility is $p^i(d, \tilde t) - \sum_{j \in x^i(d)} \tilde t_j$.
--
--   There is a mechanism $(x, p)$ such that
--   1. $x$ is an optimal allocation algorithm: $g(x(d), d) \le g(y, d)$ for every positive $d$ and every allocation $y$;
--   2. it is strongly truthful: declaring the true type and performing every task in its minimal time is dominant, and it is the only dominant strategy;
--   3. whenever every agent plays a dominant strategy, the realized make-span is at most $g(y, t)$ for every allocation $y$;
--   4. it satisfies participation constraints: for every positive $d$, every $\tilde t$ and every agent $i$,
--   $$\tilde t_j = d^i_j \ \text{ for all } j \in x^i(d) \quad\Longrightarrow\quad p^i(d, \tilde t) - \sum_{j \in x^i(d)} \tilde t_j \ge 0.$$
--
--   This is Theorem 5.4 of Nisan and Ronen (p. 190). The paper's witness is the Compensation-and-Bonus mechanism of Theorem 5.1 with the bonus shifted by $g^{-i}(d^{-i})$, the optimal make-span among allocations that give agent $i$ nothing; shifting by a term that does not depend on agent $i$'s own strategy keeps the incentives of Theorem 5.1 and makes the truthful agent's utility non-negative.
--
--   **Formalization Note** The paper's "mechanism ... for the task scheduling problem" is read as an optimal implementation, as for the generalized Compensation-and-Bonus mechanisms it is built from, so items 1 and 3 are stated. The hypothesis $n \ge 2$ is not printed: with one agent strong truthfulness fails and $g^{-i}$ is undefined. Participation uses the platform's definition (Definition 28 with $\tilde t_j = t^i_j$, the agent's own declared time).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166-196, doi:10.1006/game.1999.0790, p. 190, Theorem 5.4 (Definition 28, p. 189)

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model

open AlgMechDesign.CompBonus

theorem NisanRonen2001.thm5_4_participation_faithful {n k : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
      (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ),
      IsOptimalAlloc alloc ∧ StronglyTruthful alloc pay ∧ ImplementsOptimum alloc pay ∧
        Participation alloc pay := by sorry
