-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_clauseAverage_alive
-- name    : OAI.FixedClauseThreshold.clauseAverage_alive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:07:06.210457+00:00
-- url     : https://prove2.me/theorems/efd70a03-df63-4e65-ae1a-e865bc3861ab
-- title:
--   Exact one-step survival of a solution set under a random proper clause
-- statement:
--   Let $k\le n$. A *proper $k$-clause* on the Boolean variables $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each; $\sigma\in\{0,1\}^n$ satisfies it if it agrees with at least one of the signs, and $\operatorname{Sat}(C)$ denotes the set of assignments satisfying $C$. For $S\subseteq\{0,1\}^n$ let $\operatorname{Forced}(S)$ be the set of variables on which all members of $S$ agree (empty if $S=\emptyset$), let $b=|\operatorname{Forced}(S)|$, and let $\operatorname{alive}(T)$ be $1$ if $T\ne\emptyset$ and $0$ otherwise. If $C$ is a uniformly random proper $k$-clause, then
--
--   $$
--   \mathbb E_C\Big[\operatorname{alive}\big(S\cap\operatorname{Sat}(C)\big)\Big]=\operatorname{alive}(S)\left(1-\frac{\binom bk}{\binom nk\,2^k}\right).
--   $$
--
--   The left side is $(A_k\operatorname{alive})(S)$ for the clause-averaging operator $A_k$, i.e. the probability that some member of $S$ satisfies one more random clause. The formula shows that this one-step survival depends on $S$ only through its number of forced variables. It is the proper-clause counterpart of the auxiliary-clause formula $1-(b/2n)^k$, and comparing the two formulas is how the proper and auxiliary clause models are related.
--
--   **Formalization Note** The left side is `clauseAverage k alive S`, and the fraction is `killFraction (forcedVariables S).card n k`. The hypothesis $k\le n$ makes the set of proper $k$-clauses nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Transfer.lean#L101-L115

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

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.clauseAverage_alive {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    clauseAverage k alive S = alive S * (1 - killFraction (forcedVariables S).card n k) := by sorry
