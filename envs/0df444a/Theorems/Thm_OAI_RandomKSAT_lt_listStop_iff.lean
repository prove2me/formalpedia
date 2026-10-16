-- Prove2me | Theorems.Thm_OAI_RandomKSAT_lt_listStop_iff
-- name    : OAI.RandomKSAT.lt_listStop_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:23:42.747319+00:00
-- url     : https://prove2.me/theorems/7f4652c9-2bbe-460d-b279-a150d26c88ef
-- title:
--   Characterization of the failure time of a finite list of clauses
-- statement:
--   Fix $n,k\in\mathbb N$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. A finite list of clauses is *satisfiable* if one assignment satisfies all of its members. For a list $l=(c_1,\dots,c_L)$ of clauses and $m\in\mathbb N$ let $l_{\le m}=(c_1,\dots,c_{\min(m,L)})$ be its prefix of length $m$ (all of $l$ when $m\ge L$), and define the *failure time*
--   $$
--   \tau(l)=\min\big\{m\in\mathbb N:\ m=L+1\ \text{or}\ l_{\le m}\ \text{is not satisfiable}\big\}.
--   $$
--   Thus $\tau(l)\le L+1$, and $\tau(l)=L+1$ when $l$ itself is satisfiable.
--
--   **Theorem.** For every list $l$ of clauses, of length $L$, and every $m\in\mathbb N$,
--   $$
--   m<\tau(l)\iff m\le L\ \text{ and }\ l_{\le m}\ \text{is satisfiable}.
--   $$
--
--   Since prefixes of a satisfiable list are satisfiable, this says that $\tau(l)$ is the length of the shortest unsatisfiable prefix of $l$ (or $L+1$ if there is none), and it reduces any statement about $\tau$ to statements about satisfiability of prefixes. It is the basic tool for computing how the failure time changes when a clause is inserted into the list.
--
--   **Formalization Note** $\tau(l)$ is `listStop l`, defined by `Nat.find` for the predicate `m = l.length + 1 ∨ ¬ listSAT (l.take m)`; the prefix $l_{\le m}$ is `l.take m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderStops.lean#L36-L50

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

theorem OAI.RandomKSAT.lt_listStop_iff {n k m : ℕ} (l : List (Clause n k)) :
    m < listStop l ↔ m ≤ l.length ∧ listSAT (l.take m) := by sorry
