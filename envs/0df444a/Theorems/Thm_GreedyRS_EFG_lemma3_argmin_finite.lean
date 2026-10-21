-- Prove2me | Theorems.Thm_GreedyRS_EFG_lemma3_argmin_finite
-- name    : GreedyRS.EFG.lemma3_argmin_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:52.815367+00:00
-- url     : https://prove2.me/theorems/e6820bf9-ac66-4b01-b839-312626cc3d49
-- title:
--   Lemma 3, p. 22 — the running average of iid N(0,1) from n₀ on attains its minimum a.s.
-- statement:
--   Let $Z_1, Z_2, \dots$ be independent standard normal random variables and $\bar Z(n) = \frac1n \sum_{j=1}^n Z_j$. For every integer $n_0 \ge 1$, the process $\{\bar Z(n) : n \ge n_0\}$ reaches its minimum at a finite time almost surely:
--   $$\Pr\Big\{\arg\min_{n\ge n_0} \bar Z(n) < \infty\Big\} = 1.$$
--
--   This guarantees that the argmin $N_1^*(n_0)$ of the best alternative's running average is finite, which is the last ingredient of the EFG sample-optimality bound (Theorem 3).
--
--   **Formalization Note** $\arg\min_{n \ge n_0}$ is the first index $m \ge n_0$ with $\bar Z(m) \le \bar Z(n)$ for all $n \ge n_0$, and $\infty$ if no such index exists.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 22, Lemma 3; proof EC.2.1, p. ec6

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem lemma3_argmin_finite (n0 : ℕ) (hn0 : 1 ≤ n0) :
    ∀ᵐ z ∂GreedyRS.Greedy.stdNormalSeq, GreedyRS.Greedy.argminFrom (GreedyRS.Greedy.zbar z) n0 < ⊤ := by sorry

end GreedyRS.EFG
