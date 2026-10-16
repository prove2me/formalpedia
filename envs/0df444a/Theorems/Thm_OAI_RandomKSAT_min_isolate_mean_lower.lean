-- Prove2me | Theorems.Thm_OAI_RandomKSAT_min_isolate_mean_lower
-- name    : OAI.RandomKSAT.min_isolate_mean_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:31:20.83799+00:00
-- url     : https://prove2.me/theorems/5b3e10cc-450e-4284-b10a-a7d73fa7b0a0
-- title:
--   Truncating the isolated-clause count at $Q$ keeps a proportional share of its mean
-- statement:
--   Let $n,k,M,Q$ be natural numbers with $M\ge1$ and $Q\le M$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. Let $w=(w_0,\dots,w_{M-1})$ be a uniformly random word of $M$ clauses of width $k$ on $[n]$ (equivalently, $M$ independent uniform clauses), and call an index $i$ *isolated* if the support of $w_i$ is disjoint from the supports of all $w_j$ with $j\ne i$; let $\mathrm{Iso}(w)$ be the set of isolated indices. Let $\beta$ be a real number.
--
--   **Theorem.** If $M\beta\le\mathbb E\,|\mathrm{Iso}(w)|$, then
--   $$
--   Q\beta\le\mathbb E\big[\min\big(Q,|\mathrm{Iso}(w)|\big)\big].
--   $$
--
--   If at least a fraction $\beta$ of the $M$ clauses is isolated on average, then the count of isolated clauses truncated at $Q$ still has mean at least a fraction $\beta$ of $Q$. This converts a lower bound for the expected number of isolated clauses into the lower bound for $\mathbb E\min(Q,|\mathrm{Iso}(w)|)$ required by the bystander variance bound for the failure time of a random clause word.
--
--   **Formalization Note** Expectations are uniform averages `favg` over all words `w : Fin M → Clause n k`, and $\mathrm{Iso}(w)$ is `isolateSet w`. No relation between $k$ and $n$ is assumed: if $k>n$ there are no clauses and, by Lean's convention for the empty average, both expectations are $0$; the statement remains true because the hypothesis then forces $\beta\le0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderVariance.lean#L214-L229

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.min_isolate_mean_lower {n k M Q : ℕ} (hM : 0 < M) (hQ : Q ≤ M)
    {β : ℝ} (hmean : (M:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => ((isolateSet w).card:ℝ))) :
    (Q:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) := by sorry
