-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_comparisons
-- name    : OAI.FixedClauseThreshold.center_comparisons
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:13:58.582118+00:00
-- url     : https://prove2.me/theorems/b7e71b4e-5fa0-41ab-9fe9-38428bb26833
-- title:
--   Eventual block and neighbour comparisons for random $k$-SAT centers
-- statement:
--   Fix a clause size $k\ge 3$ and put $\delta_k=\frac{k-2}{4k}$. Let $\gamma_k(n)$ denote the *normalized center* of the random proper $k$-SAT model on $n$ variables: draw $M=2^{k+1}n$ independent uniformly random proper $k$-clauses $C_1,\dots,C_M$ (each clause uses $k$ distinct variables chosen uniformly among $x_1,\dots,x_n$, with independent fair signs), let the *satisfiable lifetime* $L_n$ be the number of indices $j\in\{1,\dots,M\}$ for which $C_1\wedge\cdots\wedge C_j$ is satisfiable, and set $\gamma_k(n)=\mathbb{E}[L_n]/n$.
--
--   **Theorem.** There exists $N\in\mathbb{N}$ such that the following two comparisons hold.
--
--   1. For all $r\ge N$ and $s\ge N$,
--   $$
--   \min\bigl(\gamma_k(r),\gamma_k(s)\bigr)-4\,\min(r,s)^{-\delta_k}\le\gamma_k(r+s).
--   $$
--   2. For all $s\ge N$,
--   $$
--   \gamma_k(s)-4\,s^{-\delta_k}\le\gamma_k(s+1).
--   $$
--
--   The first inequality is an approximate min-superadditivity of the sequence of centers and the second an approximate monotonicity under adding one variable, both with errors decaying like a negative power of the size. These are exactly the hypotheses of the convergence lemma for such sequences, and so they lead to the existence of $\lim_{n\to\infty}\gamma_k(n)$.
--
--   **Formalization Note** In Lean the error terms are `densityWindow (min r s) k` and `densityWindow s k`, where `densityWindow n k` is the real power $n^{-\delta_k}$, and $\gamma_k(n)$ is `center n k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterComparison.lean#L344-L363

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.center_comparisons (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N,
        min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k) ∧
      (∀ s ≥ N, center s k - 4 * densityWindow s k ≤ center (s + 1) k) := by sorry
