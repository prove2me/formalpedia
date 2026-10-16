-- Prove2me | Theorems.Thm_OAI_RandomKSAT_harmless_private
-- name    : OAI.RandomKSAT.harmless_private
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:24:08.079864+00:00
-- url     : https://prove2.me/theorems/2f29d131-83f5-48e7-9823-e9cd29dfd2b5
-- title:
--   A clause with a private variable is harmless for satisfiability
-- statement:
--   Fix $n,k\in\mathbb N$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. A finite list of clauses is *satisfiable* if one assignment satisfies all of its members. A list $r$ is a *sublist* of $l$ if it is obtained from $l$ by deleting some entries and keeping the order of the others. For a clause $c$ and a list $r$ write $(c,r)$ for the list with $c$ prepended to $r$. A clause $c$ is *harmless* for a list $l$ if for every sublist $r$ of $l$ the list $(c,r)$ is satisfiable if and only if $r$ is satisfiable.
--
--   **Theorem.** Let $c=(V,\beta)$ be a clause and $l$ a finite list of clauses. If some variable $v\in V$ lies in the support of no clause of $l$, then $c$ is harmless for $l$; that is, for every sublist $r$ of $l$,
--   $$
--   (c,r)\ \text{is satisfiable}\iff r\ \text{is satisfiable}.
--   $$
--
--   A clause with a private variable can always be satisfied through that variable without disturbing any other clause. Consequently, adding such a clause anywhere in a list does not change which prefixes are satisfiable apart from the shift in positions, which is how isolated clauses of a random formula (clauses whose support is disjoint from all other supports) act as bystanders in the variance lower bound for the random $k$-SAT failure time.
--
--   **Formalization Note** The private variable is given as an element `v` of the support `c.1.1` together with the hypothesis `∀ d ∈ l, v.val ∉ d.1.1`; `Harmless c l` quantifies over all `r` with `r.Sublist l`, and $(c,r)$ is `c :: r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderStops.lean#L59-L76

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

theorem OAI.RandomKSAT.harmless_private {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (v : c.1.1) (hv : ∀ d ∈ l, v.val ∉ d.1.1) : Harmless c l := by sorry
