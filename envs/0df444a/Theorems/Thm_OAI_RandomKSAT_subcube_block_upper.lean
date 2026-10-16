-- Prove2me | Theorems.Thm_OAI_RandomKSAT_subcube_block_upper
-- name    : OAI.RandomKSAT.subcube_block_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:22:50.851976+00:00
-- url     : https://prove2.me/theorems/3f18f33c-8dc8-4d15-81bb-76951d6a416f
-- title:
--   Upper bound $t\kappa+t^2k^2/u$ for the probability that $t$ random clauses kill a subcube
-- statement:
--   Let $u,b,k\in\mathbb N$ with $u>0$, $b\le u$ and $k\le u$. Assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on the variables $[u]=\{0,\dots,u-1\}$. A clause of width $k$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, and $a$ satisfies $c$ if $a(v)=\beta(v)$ for some $v\in V$. Let
--   $$
--   Q_{u,b}=\{a : a(v)=\mathrm F \text{ for every } v\in[u] \text{ with } v<b\}
--   $$
--   be the subcube of assignments that are false on the first $b$ variables, and let $\kappa(u,b,k)=\binom bk/(2^k\binom uk)$ be the kill ratio. For independent uniformly random width-$k$ clauses $c_0,c_1,\dots$ and a finite set $S$ of assignments, let $\mathrm{BK}_{u,k}(S,t)$ be the probability that no $a\in S$ satisfies all of $c_0,\dots,c_{t-1}$.
--
--   **Theorem.** For every $t\in\mathbb N$,
--   $$
--   \mathrm{BK}_{u,k}(Q_{u,b},t)\le t\,\kappa(u,b,k)+\frac{t^2k^2}{u}.
--   $$
--
--   The first term accounts for one of the $t$ clauses killing the subcube on its own (a single clause does so with probability $\kappa(u,b,k)$), and the second bounds the expected number of pairs of clauses that share a variable. When $t^2k^2/u$ is negligible compared with $t\,\kappa(u,b,k)$, the block-kill probability of the subcube is therefore essentially $t\,\kappa(u,b,k)$; together with the matching lower bound this yields the exact asymptotics of block killing used in the sharpness constructions.
--
--   **Formalization Note** $\mathrm{BK}_{u,k}(S,t)$ is `blockKill u k S t` and $Q_{u,b}$ is `subcube u b`; the right-hand side is computed in $\mathbb{R}$, with real division by $u>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/Subcube.lean#L168-L201

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

theorem OAI.RandomKSAT.subcube_block_upper {u b k : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hku : k ≤ u)
    (t : ℕ) :
    blockKill u k (subcube u b) t ≤
      (t : ℝ) * killRatio u b k + (t : ℝ)^2 * (k : ℝ)^2 / u := by sorry
