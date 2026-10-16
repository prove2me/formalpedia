-- Prove2me | Theorems.Thm_OAI_RandomKSAT_blockKill_individual
-- name    : OAI.RandomKSAT.blockKill_individual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:18:27.445182+00:00
-- url     : https://prove2.me/theorems/ec7a26c3-213e-4f00-afbf-5f37b3433c6e
-- title:
--   Block-kill probability is at least the chance that one of the $g$ clauses kills on its own
-- statement:
--   Let $u,s\in\mathbb N$ with $s\le u$. Assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on the variables $[u]=\{0,\dots,u-1\}$. A clause of width $s$ is a pair $c=(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, and $a$ satisfies $c$ if $a(v)=\beta(v)$ for some $v\in V$. Let $c_0,c_1,c_2,\dots$ be independent clauses, each uniformly distributed on the $\binom us2^s$ clauses of width $s$. For a finite set $S$ of assignments and $g\in\mathbb N$, the *block-kill probability* is
--   $$
--   \mathrm{BK}_{u,s}(S,g)=\Pr\big[\text{no } a\in S \text{ satisfies all of } c_0,\dots,c_{g-1}\big].
--   $$
--   Write $\operatorname{Fr}(S)=\{v\in[u] : a(v)=a'(v) \text{ for all } a,a'\in S\}$ for the set of frozen variables of $S$ and $\kappa(u,b,s)=\binom bs/(2^s\binom us)$ for the kill ratio.
--
--   **Theorem.** If $S$ is nonempty, then for every $g\in\mathbb N$
--   $$
--   1-\big(1-\kappa(u,|\operatorname{Fr}(S)|,s)\big)^g\le\mathrm{BK}_{u,s}(S,g).
--   $$
--
--   A single uniform clause kills $S$ (is violated by every member of $S$) with probability exactly $\kappa(u,|\operatorname{Fr}(S)|,s)$, so the left side is the probability that at least one of the $g$ clauses kills $S$ on its own. This is the lower half of the two-sided estimate of block-kill probabilities of subcubes, where it is combined with the elementary bound $1-(1-h)^g\ge gh-g^2h^2$, valid for $0\le h\le1$.
--
--   **Formalization Note** $\mathrm{BK}_{u,s}(S,g)$ is `blockKill u s S g`, the real value of the measure of the event under the infinite product of uniform measures on the finite clause type; the hypothesis $s\le u$ makes the clause type nonempty, so that this is a probability measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BlockKilling.lean#L76-L96

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.blockKill_individual {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)}
    (hS : S.Nonempty) (g : ℕ) :
    1 - (1 - killRatio u (frozen S).card s)^g ≤ blockKill u s S g := by sorry
