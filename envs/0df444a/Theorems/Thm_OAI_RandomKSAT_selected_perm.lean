-- Prove2me | Theorems.Thm_OAI_RandomKSAT_selected_perm
-- name    : OAI.RandomKSAT.selected_perm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:28:45.195983+00:00
-- url     : https://prove2.me/theorems/f1d58033-c959-4576-b1c0-9ff014606182
-- title:
--   Selected isolated clauses followed by the remaining clauses form a rearrangement of the word
-- statement:
--   Fix $n,k,M,Q\in\mathbb N$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. Let $w=(w_0,\dots,w_{M-1})$ be a word of $M$ clauses of width $k$ on $[n]$. An index $i$ is *isolated* in $w$ if the support of $w_i$ is disjoint from the support of $w_j$ for every $j\ne i$; let $\mathrm{Iso}(w)$ be the set of isolated indices. For each $w$ fix a set $I_Q(w)\subseteq\mathrm{Iso}(w)$ with exactly $\min(Q,|\mathrm{Iso}(w)|)$ elements. Let $b_Q(w)$ be the list of the clauses $w_i$ with $i\in I_Q(w)$, and $a_Q(w)$ the list of the clauses $w_i$ with $i\notin I_Q(w)$, each listed in some fixed order of its index set. Write $u\sim u'$ if the list $u'$ is a rearrangement (permutation) of the list $u$.
--
--   **Theorem.** For every $Q$ and every word $w$, the concatenation of $b_Q(w)$ and $a_Q(w)$ is a rearrangement of $w$:
--   $$
--   b_Q(w)\,a_Q(w)\ \sim\ (w_0,w_1,\dots,w_{M-1}).
--   $$
--
--   The clauses at the selected isolated indices serve as bystanders and the remaining clauses as the active part in the variance lower bound for the random $k$-SAT failure time. The theorem guarantees that this split neither loses nor duplicates clauses, so averages that are invariant under rearranging a list, such as shuffle averages and shuffle variances, may be computed from the split form.
--
--   **Formalization Note** The set $I_Q(w)$ is `chosenIsolates Q w`, obtained with `Classical.choose` from the existence of a subset of `isolateSet w` of the required size; the lists are `bystanderList Q w` and `activeList Q w`, built with `Finset.toList` (whose order is unspecified), and $\sim$ is `List.Perm`. The statement holds whatever choices are made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderVariance.lean#L152-L170

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

theorem OAI.RandomKSAT.selected_perm {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    ((bystanderList Q w)++(activeList Q w)).Perm (List.ofFn w) := by sorry
