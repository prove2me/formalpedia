-- Prove2me | Theorems.Thm_OAI_RandomKSAT_lifetime_ge_survival
-- name    : OAI.RandomKSAT.lifetime_ge_survival
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:24:36.669986+00:00
-- url     : https://prove2.me/theorems/2dfd9c55-9b52-46e5-bd72-89533428face
-- title:
--   The lifetime of a solution set is at least $t$ times its $t$-clause survival probability
-- statement:
--   Let $u,k\in\mathbb N$ with $k\le u$. Assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$; a clause of width $k$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. Let $\mathcal C_{u,k}$ be the set of these clauses and $\operatorname{Sat}(c)$ the set of assignments satisfying $c$. For a finite set $S$ of assignments define:
--
--   - the block-kill probability $\mathrm{BK}_{u,k}(S,t)=\Pr[\text{no } a\in S \text{ satisfies all of } c_0,\dots,c_{t-1}]$, where $c_0,c_1,\dots$ are independent uniform elements of $\mathcal C_{u,k}$;
--   - the survival function $\mathrm{surv}_{u,k}(S,m)=(P_k^{\,m}\mathbf 1_{\neq\emptyset})(S)$, where $(P_kf)(T)=\frac{1}{|\mathcal C_{u,k}|}\sum_{c\in\mathcal C_{u,k}}f(T\cap\operatorname{Sat}(c))$ is the clause-step operator and $\mathbf 1_{\neq\emptyset}(T)$ is $1$ if $T\neq\emptyset$ and $0$ otherwise;
--   - the lifetime $L_{u,k}(S)=\sum_{m\ge0}\mathrm{surv}_{u,k}(S,m)$.
--
--   **Theorem.** For every finite set $S$ of assignments and every $t\in\mathbb N$,
--   $$
--   t\,\big(1-\mathrm{BK}_{u,k}(S,t)\big)\le L_{u,k}(S).
--   $$
--
--   Here $\mathrm{surv}_{u,k}(S,m)$ is the probability that some member of $S$ satisfies the first $m$ random clauses, so if $T$ denotes the number of random clauses needed to empty $S$, then $\mathrm{surv}_{u,k}(S,m)=\Pr[T>m]$ and $L_{u,k}(S)=\mathbb E[T]$. The inequality is the elementary bound $\mathbb E[T]\ge t\Pr[T>t]$; it converts an upper bound on block killing into a lower bound on the lifetime.
--
--   **Formalization Note** The lifetime is the Lean `tsum` `lifetime u k S`, which by convention would be $0$ for a non-summable family; for $k\le u$ the series converges, so $L_{u,k}(S)$ is the genuine sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SharpnessEstimates.lean#L12-L30

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

theorem OAI.RandomKSAT.lifetime_ge_survival {u k : ℕ} (hku : k ≤ u) (S : Finset (Assignment u)) (t : ℕ) :
    (t : ℝ) * (1 - blockKill u k S t) ≤ lifetime u k S := by sorry
