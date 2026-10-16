-- Prove2me | Theorems.Thm_OAI_RandomKSAT_replacement_gap_scaled_limit
-- name    : OAI.RandomKSAT.replacement_gap_scaled_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:29:02.439024+00:00
-- url     : https://prove2.me/theorems/c29c0128-9c77-4018-88df-4b6dc6af468c
-- title:
--   One random $(k-1)$-clause versus $g$ random $k$-clauses on a subcube: the kill-probability gap is asymptotic to $2^{-k}g^{-(k-1)}$
-- statement:
--   Let $k\ge3$ be an integer. For $u\in\mathbb N$ and a width $s$, assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$, and a clause of width $s$ is a pair $(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. For a finite set $S$ of assignments and $t\in\mathbb N$, let $\mathrm{BK}_{u,s}(S,t)$ be the probability that no member of $S$ satisfies all of $t$ independent uniformly random clauses of width $s$. Let $Q_{u,b}=\{a: a(v)=\mathrm F\text{ for all } v<b\}$ be the subcube of assignments false on the first $b$ variables, and put $u_g=g^{k+2}$ and $Q_g=Q_{g^{k+2},\,g^{k+1}}$.
--
--   **Theorem.**
--   $$
--   \lim_{g\to\infty}g^{k-1}\Big(\mathrm{BK}_{u_g,k-1}\big(Q_g,1\big)-\mathrm{BK}_{u_g,k}\big(Q_g,g\big)\Big)=\frac{1}{2^k},
--   $$
--   where $g$ runs through the natural numbers.
--
--   In words: on the subcube $Q_g$, a single random clause of width $k-1$ kills with a probability that exceeds the kill probability of a block of $g$ random clauses of width $k$ by $(1+o(1))\,2^{-k}g^{-(k-1)}$. Consequently, in an inequality $\mathrm{BK}_{u,k-1}(S,1)-e(g)\le\mathrm{BK}_{u,k}(S,g)$ required for all $u\ge k$, all nonempty $S$ and all $g\ge2$, the error $e(g)$ cannot be $o(g^{-(k-1)})$.
--
--   **Formalization Note** The width $k-1$ and the exponent $k-1$ are natural-number subtractions, which are exact since $k\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ReplacementSharpness.lean#L67-L86

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

theorem OAI.RandomKSAT.replacement_gap_scaled_limit (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun g : ℕ => (g : ℝ)^(k-1) *
      (blockKill (g^(k+2)) (k-1) (subcube (g^(k+2)) (g^(k+1))) 1 -
       blockKill (g^(k+2)) k (subcube (g^(k+2)) (g^(k+1))) g))
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by sorry
