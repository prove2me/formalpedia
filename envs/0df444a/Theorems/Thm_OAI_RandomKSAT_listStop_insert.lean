-- Prove2me | Theorems.Thm_OAI_RandomKSAT_listStop_insert
-- name    : OAI.RandomKSAT.listStop_insert
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:25:39.037417+00:00
-- url     : https://prove2.me/theorems/4cb939a6-f1c3-4400-a977-090857f42d9e
-- title:
--   Inserting a harmless clause delays the failure time by one exactly when it lands before the failure
-- statement:
--   Fix $n,k\in\mathbb N$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. A finite list of clauses is *satisfiable* if one assignment satisfies all of its members. For a list $l=(c_1,\dots,c_L)$ of clauses let $l_{\le m}=(c_1,\dots,c_{\min(m,L)})$ denote its prefix of length $m$, and let the *failure time* $\tau(l)$ be the least $m\in\mathbb N$ such that $m=L+1$ or $l_{\le m}$ is not satisfiable; so $\tau(l)$ is the length of the shortest unsatisfiable prefix of $l$, and $\tau(l)=L+1$ if $l$ is satisfiable. A list $r$ is a *sublist* of $l$ if it is obtained from $l$ by deleting some entries and keeping the order of the others. For a clause $c$ and a list $r$ write $(c,r)$ for the list with $c$ prepended to $r$. A clause $c$ is *harmless* for a list $l$ if for every sublist $r$ of $l$ the list $(c,r)$ is satisfiable if and only if $r$ is satisfiable. Finally, for $0\le i\le L$ let $l\oplus_i c=(c_1,\dots,c_i,c,c_{i+1},\dots,c_L)$ be the list obtained by inserting $c$ after the first $i$ entries of $l$.
--
--   **Theorem.** If $c$ is harmless for $l=(c_1,\dots,c_L)$ and $0\le i\le L$, then
--   $$
--   \tau(l\oplus_i c)=\tau(l)+\mathbf 1[i<\tau(l)].
--   $$
--
--   In words: a harmless clause inserted before the failure time postpones the failure by exactly one step, and inserted at or after the failure time it leaves the failure time unchanged. If the position $i$ is uniform among the $L+1$ slots, the shift is therefore a Bernoulli variable with mean $\tau(l)/(L+1)$; this is the elementary source of randomness behind the linear variance lower bound for the random $k$-SAT failure time.
--
--   **Formalization Note** $\tau(l)$ is `listStop l`, the inserted list is `l.insertIdx i c`, and the indicator is written `if i < listStop l then 1 else 0`; the identity is an equality of natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderStops.lean#L117-L139

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.listStop_insert {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (hc : Harmless c l) (i : ℕ) (hi : i ≤ l.length) :
    listStop (l.insertIdx i c) = listStop l + if i < listStop l then 1 else 0 := by sorry
