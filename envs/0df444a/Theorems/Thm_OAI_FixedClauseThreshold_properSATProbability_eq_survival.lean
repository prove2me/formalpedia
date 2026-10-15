-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_eq_survival
-- name    : OAI.FixedClauseThreshold.properSATProbability_eq_survival
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:50:27.539007+00:00
-- url     : https://prove2.me/theorems/583bb9fd-7c35-4de9-9d4f-9aad78ea6489
-- title:
--   The random $k$-SAT satisfiability probability equals the $m$-fold clause-averaging survival of the full cube
-- statement:
--   Fix $n,k,m\in\mathbb N$. A *proper $k$-clause* on the Boolean variables $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each; an assignment $\sigma\in\{0,1\}^n$ satisfies it if it agrees with the sign on at least one chosen variable. Let $\mathcal C_{n,k}$ be the finite set of proper $k$-clauses and $\operatorname{Sat}(C)\subseteq\{0,1\}^n$ the set of assignments satisfying $C$. A formula is an $m$-tuple $F\in\mathcal C_{n,k}^m$, and
--
--   $$
--   P_{n,k}(m)=\frac{\#\{F\in\mathcal C_{n,k}^m:\ F\text{ is satisfiable}\}}{\#\,\mathcal C_{n,k}^m}
--   $$
--
--   is the probability that $m$ independent uniformly random proper $k$-clauses are simultaneously satisfiable.
--
--   For a real function $f$ on subsets of $\{0,1\}^n$ define the clause-averaging operator $A_k$ and the nonemptiness indicator by
--
--   $$
--   (A_k f)(S)=\frac{1}{|\mathcal C_{n,k}|}\sum_{C\in\mathcal C_{n,k}} f\big(S\cap\operatorname{Sat}(C)\big),\qquad \operatorname{alive}(S)=\begin{cases}1,&S\ne\emptyset,\\0,&S=\emptyset,\end{cases}
--   $$
--
--   and the survival function $s_{k,m}(S)=(A_k^{\,m}\operatorname{alive})(S)$. Then
--
--   $$
--   P_{n,k}(m)=s_{k,m}\big(\{0,1\}^n\big).
--   $$
--
--   The survival function $s_{k,m}(S)$ is the probability that some assignment in $S$ satisfies $m$ further independent random clauses. The identity rewrites the satisfiability of a random formula as $m$ applications of a single linear and monotone operator to the indicator of nonemptiness of the solution set. This is the form used for one-clause-at-a-time recursions, for comparisons between different clause operators and for commutation arguments.
--
--   **Formalization Note** Averages are `uniformMean`, the sum divided by the cardinality, so an average over an empty set is $0$; likewise $P_{n,k}(m)$ is a $0/0=0$ quotient when $m>0$ and $n<k$. The identity holds for all $n,k,m$ without hypotheses (both sides are $1$ for $m=0$, and both are $0$ when $m>0$ and $n<k$). In Lean $s_{k,m}$ is `survival k m`, defined as `((clauseAverage k)^[m] alive)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/ClauseProcess.lean#L179-L191

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.properSATProbability_eq_survival (n k m : ℕ) :
    properSATProbability n k m = survival k m (Finset.univ : Finset (Assignment n)) := by sorry
