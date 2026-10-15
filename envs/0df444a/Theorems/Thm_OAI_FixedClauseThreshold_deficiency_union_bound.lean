-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_deficiency_union_bound
-- name    : OAI.FixedClauseThreshold.deficiency_union_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:00:41.940112+00:00
-- url     : https://prove2.me/theorems/9d7995cf-5460-45fa-a09f-ab4f882e461a
-- title:
--   Hall-deficiency union bound for the unsatisfiability of sparse random $k$-SAT
-- statement:
--   Let $n,k,m$ be natural numbers with $k\le n$, $n\ge1$ and $m\le n$. A *proper $k$-clause* on the Boolean variables $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each; an assignment satisfies it if it agrees with at least one of the signs. Let $P_{n,k}(m)$ be the probability that $m$ independent uniformly random proper $k$-clauses are simultaneously satisfiable. Then
--
--   $$
--   1-P_{n,k}(m)\ \le\ \sum_{s=1}^{m}\binom ms\binom ns\Big(\frac sn\Big)^{ks}.
--   $$
--
--   The $s$-th term bounds the expected number of pairs $(J,T)$ consisting of a set $J$ of $s$ clauses and a set $T$ of $s$ variables such that every clause in $J$ uses only variables from $T$. Such a pair violates Hall's condition for matching clauses to distinct variables, and an unsatisfiable formula with at most $n$ clauses must contain one. For sparse formulas the right-hand side is small; for instance, for $k\ge3$ and $m\le e^{-2}n/4$ it is at most $1/n$, so such formulas are satisfiable with high probability.
--
--   **Formalization Note** The sum is written as $\sum_{t=0}^{m-1}$ with $s=t+1$. $P_{n,k}(m)$ is `properSATProbability n k m`, a cardinality ratio over all $m$-tuples of proper clauses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterBounds.lean#L319-L364

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

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.deficiency_union_bound {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n) (hmn : m ≤ n) :
    1 - properSATProbability n k m ≤
      ∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
        (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1)) := by sorry
