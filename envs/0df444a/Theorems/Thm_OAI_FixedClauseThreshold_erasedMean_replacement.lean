-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_erasedMean_replacement
-- name    : OAI.FixedClauseThreshold.erasedMean_replacement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:55:28.604072+00:00
-- url     : https://prove2.me/theorems/2cf1b917-2726-422c-a1e7-4c5a4f063f19
-- title:
--   Erasing a variable from random $k$-clauses: a binomial replacement lower bound
-- statement:
--   Let $k\ge3$, $n\ge k+1$ and $m\in\mathbb N$. Consider the Boolean variables $x_0,x_1,\dots,x_{n-1}$; a *proper $r$-clause* is a choice of $r$ distinct variables with a sign (a required truth value) for each, and an assignment satisfies it if it agrees with at least one of the signs. Let $S\subseteq\{0,1\}^{n-1}$ be a set of assignments of $x_1,\dots,x_{n-1}$.
--
--   Let $C_1,\dots,C_m$ be independent uniformly random proper $k$-clauses on all $n$ variables, and *erase* $x_0$: a clause not containing $x_0$ is kept as it is, and a clause containing $x_0$ is replaced by the proper $(k-1)$-clause on $x_1,\dots,x_{n-1}$ obtained by deleting its literal on $x_0$. Let $E_m(S)$ be the probability that some $\sigma\in S$ satisfies all $m$ erased clauses. Let $s_{k,t}(S)$ be the probability that some $\sigma\in S$ satisfies $t$ independent uniformly random proper $k$-clauses on $x_1,\dots,x_{n-1}$, and put
--
--   $$
--   g=\big\lceil 2k\,n^{1/k}\big\rceil,\qquad \varepsilon=n^{-(k-1)/k}.
--   $$
--
--   Then
--
--   $$
--   \mathbb E_{D\sim\operatorname{Bin}(m,\,k/n)}\Big[s_{k,\,m-D+gD}(S)-D\,\varepsilon\Big]\ \le\ E_m(S).
--   $$
--
--   Here $D$ has the law of the number of clauses containing $x_0$. The inequality says that, up to an error $\varepsilon$ per shortened clause, the erased formula keeps a solution in $S$ at least as often as a formula of proper $k$-clauses in which each shortened clause is replaced by a block of $g$ fresh $k$-clauses. With $S$ the full cube it gives a lower bound on the satisfiability of the erased formula, which is the ingredient used to bound how often $x_0$ is forced in a random formula.
--
--   **Formalization Note** $E_m(S)$ is `erasedMean _ m S`, an average over `Formula n k m` (with $n$ written as `n - 1 + 1`) of `alive` applied to the erased solution set; $s_{k,t}$ is `survival k t`, $g$ is `replacementBlock n k` and $\varepsilon$ is `replacementError n k`. The binomial expectation is `binomialMean (k / n) m`, defined by its first-trial recursion; inside it $D\le m$, so the natural-number subtraction $m-D$ is exact.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Forcing.lean#L265-L316

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.erasedMean_replacement {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    binomialMean ((k : ℝ) / n) m (fun d =>
      survival k (m - d + replacementBlock n k * d) S -
        (d : ℝ) * replacementError n k) ≤ erasedMean (by omega : 0 < k) m S := by sorry
