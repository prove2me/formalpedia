-- Prove2me | Theorems.Thm_OAI_RandomKSAT_one_replacement
-- name    : OAI.RandomKSAT.one_replacement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:56:12.389764+00:00
-- url     : https://prove2.me/theorems/bdee5f39-e972-47c0-9b4d-e84324ebda77
-- title:
--   One random $r$-clause kills a solution set no more often than $g$ random $(r+1)$-clauses, up to $(2^{r+1}r/g)^r$
-- statement:
--   Fix natural numbers $u$ and $s$. An *assignment* is a map $a:[u]\to\{\mathrm T,\mathrm F\}$ on the variables $[u]=\{0,\dots,u-1\}$, and a *clause of width $s$* is a pair $(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. For a finite set $S$ of assignments and $g\in\mathbb N$ let
--   $$
--   B_s(S,g)=\Pr\big[\text{no }a\in S\text{ satisfies all of }c_1,\dots,c_g\big],
--   $$
--   where $c_1,\dots,c_g$ are independent uniformly random clauses of width $s$; this is the probability that a block of $g$ random clauses *kills* $S$.
--
--   **Theorem.** Let $u,r,g$ be natural numbers with $r\ge2$, $r+1\le u$ and $g\ge1$. Then for every finite set $S$ of assignments of the $u$ variables,
--   $$
--   B_r(S,1)-\frac{(2^{r+1}r)^r}{g^r}\le B_{r+1}(S,g).
--   $$
--
--   Up to the additive error $(2^{r+1}r/g)^r$, a single random clause of width $r$ is thus no more likely to kill a solution set than a block of $g$ random clauses of width $r+1$, uniformly over all solution sets. Applied clause by clause, this allows a random formula of width-$r$ clauses to be compared with a longer random formula of width-$(r+1)$ clauses.
--
--   **Formalization Note** $B_s(S,g)$ is `blockKill u s S g`, the probability (as a real number), under the law `streamLaw u s` of an infinite sequence of independent uniform clauses, that no member of $S$ satisfies the first $g$ clauses. The error term is `replacementK (r+1)/g^r` with `replacementK (r+1)` $=(2^{r+1}r)^r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BlockKilling.lean#L277-L293

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.one_replacement {u r g : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hg : 1 ≤ g)
    (S : Finset (Assignment u)) :
    blockKill u r S 1 - replacementK (r+1)/(g : ℝ)^r ≤ blockKill u (r+1) S g := by sorry
