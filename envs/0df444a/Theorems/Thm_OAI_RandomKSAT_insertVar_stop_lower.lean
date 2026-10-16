-- Prove2me | Theorems.Thm_OAI_RandomKSAT_insertVar_stop_lower
-- name    : OAI.RandomKSAT.insertVar_stop_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:27:46.827111+00:00
-- url     : https://prove2.me/theorems/3795ec36-27ba-47b9-b3fa-618957e87992
-- title:
--   Randomly inserting $q$ bystander clauses gives the failure time variance at least $q\,AC/D^2$
-- statement:
--   Fix $n,k\in\mathbb N$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. A finite list of clauses is *satisfiable* if one assignment satisfies all of its members. For a list $l=(c_1,\dots,c_L)$ of clauses let $l_{\le m}=(c_1,\dots,c_{\min(m,L)})$ denote its prefix of length $m$, and let the *failure time* $\tau(l)$ be the least $m\in\mathbb N$ such that $m=L+1$ or $l_{\le m}$ is not satisfiable; so $\tau(l)$ is the length of the shortest unsatisfiable prefix of $l$, and $\tau(l)=L+1$ if $l$ is satisfiable.
--
--   Let $b=(c_1,\dots,c_q)$ and $l$ be finite lists of clauses. The *random insertion* of $b$ into $l$ produces a random list $R$ as follows: starting from $l$, insert $c_q$ at a uniformly random one of the $|l|+1$ slots, then insert $c_{q-1}$ at a uniformly random slot of the resulting list, and so on, finally $c_1$, all choices being independent; thus $R$ has length $q+|l|$. Write $\operatorname{Var}_{b,l}$ for the variance with respect to this randomness. The list $b$ consists of *bystanders* for $l$ if for every $j$ the clause $c_j$ has a variable in its support that occurs in the support of none of the clauses $c_{j+1},\dots,c_q$ and of none of the clauses of $l$.
--
--   **Theorem.** Let $b$ be a list of bystanders for $l$, and let $A,C,D$ be real numbers with $C\ge0$, $D>0$ and
--   $$
--   A\le\tau(l),\qquad C\le|l|+1-\tau(l),\qquad |b|+|l|+1\le D .
--   $$
--   Then
--   $$
--   |b|\cdot\frac{A\,C}{D^2}\le\operatorname{Var}_{b,l}\big(\tau(R)\big).
--   $$
--
--   Each bystander inserted at a random position shifts the failure time by a Bernoulli amount, and the theorem says that the variances contributed by the successive insertions add up: the total variance is at least $|b|$ times a uniform lower bound for the variance of a single shift. With $A$ of the order of the failure time, $C$ of the order of the number of clauses after the failure and $D$ of the order of the total length, this produces a variance of order $|b|$.
--
--   **Formalization Note** The variance is `insertVar b l (fun r => (listStop r : ℝ))`, where `insertVar b l f` is `insertAvg b l (f^2) - (insertAvg b l f)^2`, `insertAvg (c :: b) l f = insertAvg b l (insertKernel c f)` and `insertKernel c f r` is the average of `f (r.insertIdx i c)` over the slots `i ≤ r.length`; this recursion inserts the last clause of $b$ first. The bystander condition is the recursively defined predicate `Bystanders b l`. No sign condition on $A$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/InsertionVariance.lean#L233-L292

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.insertVar_stop_lower {n k : ℕ} {b l : List (Clause n k)} (hb : Bystanders b l)
    {A C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hAt : A ≤ (listStop l:ℝ)) (hCt : C ≤ (l.length:ℝ)+1-listStop l)
    (hlen : (b.length:ℝ)+l.length+1 ≤ D) :
    (b.length:ℝ)*(A*C/D^2) ≤ insertVar b l (fun r => (listStop r:ℝ)) := by sorry
