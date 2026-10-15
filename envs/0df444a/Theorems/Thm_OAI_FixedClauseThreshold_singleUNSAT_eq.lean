-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_singleUNSAT_eq
-- name    : OAI.FixedClauseThreshold.singleUNSAT_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:53:05.240698+00:00
-- url     : https://prove2.me/theorems/9c4343aa-8300-4910-b19e-6b080bf04c39
-- title:
--   Killing probability of one random proper clause equals one minus the one-step survival
-- statement:
--   Let $k\le n$ be natural numbers. A *proper $k$-clause* on the Boolean variables $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each; $\sigma\in\{0,1\}^n$ satisfies it if it agrees with the sign on at least one chosen variable. Write $\mathcal C_{n,k}$ for the set of proper $k$-clauses and $\operatorname{Sat}(C)$ for the set of assignments satisfying $C$. For $S\subseteq\{0,1\}^n$ say that $C$ *kills* $S$ if no member of $S$ satisfies $C$. Let $\operatorname{alive}(T)$ be $1$ if $T\neq\emptyset$ and $0$ otherwise, and let
--
--   $$
--   s_{k,1}(S)=\frac{1}{|\mathcal C_{n,k}|}\sum_{C\in\mathcal C_{n,k}}\operatorname{alive}\big(S\cap\operatorname{Sat}(C)\big)
--   $$
--
--   be the one-step survival function, the probability that some member of $S$ satisfies one random clause. Then for every $S\subseteq\{0,1\}^n$, with $C$ uniform on $\mathcal C_{n,k}$,
--
--   $$
--   \Pr\big[\,C\text{ kills }S\,\big]=1-s_{k,1}(S).
--   $$
--
--   The statement translates the event that a single random clause destroys all remaining solutions into the language of survival functions, so that killing probabilities computed by counting can be inserted into survival recursions. For $S=\emptyset$ both sides equal $1$.
--
--   **Formalization Note** The hypothesis $k\le n$ guarantees that $\mathcal C_{n,k}$ is nonempty, so that averaging the constant $1$ gives $1$. In Lean the left side is `uniformProbability (fun C => KillsSolutions S C)` and $s_{k,1}$ is `survival k 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/ClauseProcess.lean#L303-L316

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.singleUNSAT_eq {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    uniformProbability (fun C : ProperClause n k => KillsSolutions S C) =
      1 - survival k 1 S := by sorry
