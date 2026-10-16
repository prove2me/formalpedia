-- Prove2me | Theorems.Thm_OAI_RandomKSAT_lifetime_product
-- name    : OAI.RandomKSAT.lifetime_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:56:46.402967+00:00
-- url     : https://prove2.me/theorems/cb598266-e52f-43a1-a256-9bf549886fb9
-- title:
--   Lifetime of a solution set under random $(r+1)$-clauses versus its killing probability by $d$ random $r$-clauses
-- statement:
--   Fix $u\in\mathbb N$. An *assignment* is a map $a:[u]\to\{\mathrm T,\mathrm F\}$ on the variables $[u]=\{0,\dots,u-1\}$, and a *clause of width $s$* is a pair $(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. For a finite set $S$ of assignments and $s,m\in\mathbb N$ let
--
--   - $\sigma_s(S,m)$ be the probability that some $a\in S$ satisfies all of $m$ independent uniformly random clauses of width $s$ (the *survival probability* of $S$);
--   - $\Lambda_s(S)=\sum_{m\ge0}\sigma_s(S,m)$ be the *lifetime* of $S$, i.e. the expected number of independent random width-$s$ clauses that $S$ survives (the expected first time at which no member of $S$ satisfies all clauses so far);
--   - $B_s(S,d)$ be the probability that $d$ independent uniformly random clauses of width $s$ kill $S$, i.e. no member of $S$ satisfies all of them.
--
--   **Theorem.** Let $u,r,d$ be natural numbers with $r\ge2$, $r+1\le u$ and $d\ge1$. Then for every finite set $S$ of assignments,
--   $$
--   \Lambda_{r+1}(S)\,B_r(S,d)^{(r+1)/r}\le C_{r+1}\,d^{(r+1)/r},\qquad C_{r+1}=4\big(2(2^{r+1}r)^r\big)^{1/r}=2^{r+3+1/r}\,r .
--   $$
--
--   Equivalently, if $d$ random clauses of width $r$ kill $S$ with probability $q>0$, then on average $S$ survives at most $C_{r+1}(d/q)^{(r+1)/r}$ random clauses of width $r+1$. The bound turns killing estimates for shorter clauses into lifetime estimates for longer ones, uniformly in $S$; such lifetime bounds serve as potentials for controlling how long the evolving solution set of a random formula stays in a given state.
--
--   **Formalization Note** $\sigma_s(S,m)$ is `survival u s S m`, defined as the $m$-th iterate of the one-clause averaging operator `clauseStep u s` applied to the indicator `alive u` of nonemptiness; $\Lambda_s(S)$ is `lifetime u s S`, a `tsum` (the series converges here); $B_r(S,d)$ is `blockKill u r S d`. The exponent is `lifetimeBeta (r+1)` $=(r+1)/r$ and the constant is `lifetimeC (r+1)` $=4(2K)^{1/r}$ with $K=$ `replacementK (r+1)` $=(2^{r+1}r)^r$, both computed with the natural subtraction $(r+1)-1=r$. Powers are real powers; when $B_r(S,d)=0$ the left-hand side is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/MarkovReplacement.lean#L381-L425

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.lifetime_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (S : Finset (Assignment u)) :
    lifetime u (r+1) S * (blockKill u r S d)^(lifetimeBeta (r+1)) ≤
      lifetimeC (r+1) * (d : ℝ)^(lifetimeBeta (r+1)) := by sorry
