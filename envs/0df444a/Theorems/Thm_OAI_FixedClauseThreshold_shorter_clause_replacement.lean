-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_shorter_clause_replacement
-- name    : OAI.FixedClauseThreshold.shorter_clause_replacement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:49:59.401434+00:00
-- url     : https://prove2.me/theorems/be46b030-a4d5-4757-a3f5-07a10f55d39e
-- title:
--   A shorter random clause is dominated by a block of longer random clauses up to error $n^{-(k-1)/k}$
-- statement:
--   Let $k\ge 3$ and $n\ge k+1$ be integers and put $v=n-1$. A *proper $r$-clause* on the Boolean variables $x_1,\dots,x_v$ is a choice of $r$ distinct variables together with a sign (a required truth value) for each of them; an assignment $\sigma\in\{0,1\}^v$ satisfies it if $\sigma$ agrees with the sign on at least one chosen variable. For a set $S\subseteq\{0,1\}^v$ of assignments, a clause $Q$ *kills* $S$ if no $\sigma\in S$ satisfies $Q$ (every clause kills $S=\emptyset$).
--
--   Set
--
--   $$
--   a=n^{1/k},\qquad \varepsilon_{n,k}=a^{-(k-1)}=n^{-(k-1)/k},\qquad g=\lceil 2k\,a\rceil .
--   $$
--
--   Let $Q$ be a uniformly random proper $(k-1)$-clause on $x_1,\dots,x_v$, and let $C_1,\dots,C_g$ be independent uniformly random proper $k$-clauses on the same variables. Then for every $S\subseteq\{0,1\}^v$,
--
--   $$
--   \Pr\big[\,Q\text{ kills }S\,\big]-\varepsilon_{n,k}\;\le\;\Pr\big[\,\text{no }\sigma\in S\text{ satisfies all of }C_1,\dots,C_g\,\big].
--   $$
--
--   Thus a single clause of length $k-1$ can be traded for a block of $g\approx 2k\,n^{1/k}$ fresh clauses of length $k$, at an additive cost $\varepsilon_{n,k}$ that does not depend on $S$. The uniformity in $S$ is what allows the comparison to be applied inside a random clause process, where $S$ is the random set of assignments that survive the clauses drawn so far; when a variable is erased from the clauses containing it, each shortened clause is replaced by such a block, at a total cost of $\varepsilon_{n,k}$ per shortened clause (note $n\,\varepsilon_{n,k}=n^{1/k}$).
--
--   **Formalization Note** The right-hand side is `blockUNSATProbability k (replacementBlock n k) S`, the fraction of formulas in `Formula (n - 1) k g` with no satisfying assignment in `S`; $a$, $\varepsilon_{n,k}$ and $g$ are `replacementScale n k`, `replacementError n k` and `replacementBlock n k`. Probabilities are cardinality ratios (`uniformProbability`), and the variables are indexed by `Fin (n - 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Replacement.lean#L324-L374

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.shorter_clause_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    uniformProbability (fun Q : ProperClause (n - 1) (k - 1) => KillsSolutions S Q) -
      replacementError n k ≤ blockUNSATProbability k (replacementBlock n k) S := by sorry
