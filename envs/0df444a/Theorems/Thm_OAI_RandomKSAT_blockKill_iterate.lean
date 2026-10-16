-- Prove2me | Theorems.Thm_OAI_RandomKSAT_blockKill_iterate
-- name    : OAI.RandomKSAT.blockKill_iterate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:19:41.43789+00:00
-- url     : https://prove2.me/theorems/58520ab4-1f34-4862-ae15-9fa9182cef73
-- title:
--   Block-kill probability equals one minus the iterated clause-step operator on the nonemptiness indicator
-- statement:
--   Let $u,s\in\mathbb N$ with $s\le u$. Assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$; a clause of width $s$ is a pair $c=(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ if $a(v)=\beta(v)$ for some $v\in V$. Let $\mathcal C_{u,s}$ be the set of these clauses and $\operatorname{Sat}(c)$ the set of assignments satisfying $c$. Let $c_0,c_1,\dots$ be independent uniformly random elements of $\mathcal C_{u,s}$, and for a finite set $S$ of assignments and $g\in\mathbb N$ let
--   $$
--   \mathrm{BK}_{u,s}(S,g)=\Pr\big[\text{no } a\in S \text{ satisfies all of } c_0,\dots,c_{g-1}\big]
--   $$
--   be the block-kill probability. The clause-step operator $P_s$ sends a function $f$ on finite sets of assignments to $(P_sf)(S)=\frac{1}{|\mathcal C_{u,s}|}\sum_{c\in\mathcal C_{u,s}}f(S\cap\operatorname{Sat}(c))$, and $\mathbf 1_{\neq\emptyset}(T)$ equals $1$ if $T\neq\emptyset$ and $0$ if $T=\emptyset$.
--
--   **Theorem.** For every finite set $S$ of assignments and every $m\in\mathbb N$,
--   $$
--   \mathrm{BK}_{u,s}(S,m)=1-\big(P_s^{\,m}\mathbf 1_{\neq\emptyset}\big)(S).
--   $$
--
--   Equivalently, the probability that $S$ still has a common satisfying assignment after $m$ independent random clauses is obtained by running the clause-filtering Markov chain for $m$ steps and evaluating the indicator of nonemptiness. This identifies the measure-theoretic block-kill probability with the purely combinatorial survival function $m\mapsto(P_s^{\,m}\mathbf 1_{\neq\emptyset})(S)$, whose sum over $m$ is the lifetime of $S$.
--
--   **Formalization Note** $\mathrm{BK}_{u,s}(S,m)$ is `blockKill u s S m`, defined through the infinite product of uniform measures on the clause type, and $\mathbf 1_{\neq\emptyset}$ is `alive u`. The hypothesis $s\le u$ makes the clause type nonempty, so that the product measure is a probability measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/MarkovReplacement.lean#L132-L147

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.blockKill_iterate {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    blockKill u s S m = 1 - (clauseStep u s)^[m] (alive u) S := by sorry
