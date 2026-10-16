-- Prove2me | Theorems.Thm_OAI_RandomKSAT_replacement_scaled_limit
-- name    : OAI.RandomKSAT.replacement_scaled_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:27:08.502936+00:00
-- url     : https://prove2.me/theorems/f8a0663a-6e38-4eaa-be24-473ad7e9ca20
-- title:
--   A block of $g$ random $k$-clauses kills a subcube with probability asymptotic to $2^{-k}g^{-(k-1)}$
-- statement:
--   Let $k\ge3$ be an integer. For $u\in\mathbb N$, assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$, and a clause of width $k$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. For a finite set $S$ of assignments and $t\in\mathbb N$, let $\mathrm{BK}_{u,k}(S,t)$ be the probability that no member of $S$ satisfies all of $t$ independent uniformly random clauses of width $k$. Let $Q_{u,b}=\{a: a(v)=\mathrm F\text{ for all } v<b\}$ be the subcube of assignments that are false on the first $b$ variables.
--
--   **Theorem.** With $u_g=g^{k+2}$ variables and the subcube $Q_g=Q_{g^{k+2},\,g^{k+1}}$,
--   $$
--   \lim_{g\to\infty}g^{k-1}\,\mathrm{BK}_{u_g,k}\big(Q_g,\,g\big)=\frac{1}{2^k},
--   $$
--   where $g$ runs through the natural numbers.
--
--   So a block of $g$ random clauses of width $k$ kills $Q_g$ with probability asymptotic to $2^{-k}g^{-(k-1)}$, which is $g$ times the asymptotic probability $2^{-k}g^{-k}$ that a single such clause kills $Q_g$. This is the width-$k$ half of the comparison, on the same subcube, between one random clause of width $k-1$ and a block of $g$ random clauses of width $k$.
--
--   **Formalization Note** The exponent $k-1$ is natural-number subtraction, which is exact since $k\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ReplacementSharpness.lean#L19-L65

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

theorem OAI.RandomKSAT.replacement_scaled_limit (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun g : ℕ => (g : ℝ)^(k-1) * blockKill (g^(k+2)) k
      (subcube (g^(k+2)) (g^(k+1))) g) atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by sorry
