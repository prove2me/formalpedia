-- Prove2me | Theorems.Thm_OAI_RandomKSAT_scheduled_reward_integrated_critical
-- name    : OAI.RandomKSAT.scheduled_reward_integrated_critical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:02:51.297482+00:00
-- url     : https://prove2.me/theorems/6f8f98c5-ab93-414f-b6fa-cc62594c7561
-- title:
--   Logarithmic bound for cumulative rewards along a scheduled clause-filtering process
-- statement:
--   Fix natural numbers $k\le u$. An *assignment* is a map $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$, and a *clause of width $k$* is a pair $(V,\beta)$ of a $k$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; write $\mathrm{Sat}(c)$ for the set of assignments $a$ with $a(v)=\beta(v)$ for some $v\in V$. All sets $S,T$ below are finite sets of assignments.
--
--   *Lifetime.* $\Lambda(S)=\sum_{m\ge0}\Pr\big[\text{some } a\in S \text{ satisfies } c_1,\dots,c_m\big]$, where $c_1,c_2,\dots$ are independent uniformly random clauses of width $k$; it is the expected number of random clauses that $S$ survives.
--
--   *Schedule.* A schedule consists of a set of *ordinary* time indices $i\in\mathbb N$ and masks $D_i$ (sets of assignments) for all $i$. The step operator at time $i$ acts on real functions $\varphi$ of sets of assignments by $(P_i\varphi)(S)=\mathbb E_c\,\varphi\big(S\cap\mathrm{Sat}(c)\big)$, with $c$ a uniformly random clause of width $k$, if $i$ is ordinary, and by $(P_i\varphi)(S)=\varphi(S\cap D_i)$ otherwise. For a reward $f$ the cumulative reward is defined by $\mathcal M_0(P,f)=0$ and $\mathcal M_{m+1}(P,f)=f+P_0\big(\mathcal M_m(P^{+},f)\big)$ with $P^{+}=(P_{i+1})_i$. It equals the expected total reward $\mathbb E\sum_{i=0}^{m-1}f(S_i)$ of the process $S_0=S$, $S_{i+1}=S_i\cap\mathrm{Sat}(c_i)$ with a fresh independent clause $c_i$ at ordinary steps, and $S_{i+1}=S_i\cap D_i$ at the other steps.
--
--   **Theorem.** Let $f$ be a real function on sets of assignments with $f(\emptyset)=0$ and $0\le f\le1$, and let $Q,Z\ge0$ be real numbers with $\Lambda(T)\,f(T)\le Q$ for every $T$. Let $L\ge1$ be such that at most $Z$ of the indices $0,\dots,L-1$ are not ordinary. Then for every $S$,
--   $$
--   \mathcal M_L(P,f)(S)\le(Q+Z+1)\,(1+\log L).
--   $$
--
--   A reward that is inversely proportional to the expected remaining lifetime can therefore accumulate only logarithmically in the length $L$ of the process, even when deterministic restriction steps are interspersed, each of which costs at most one unit. Such bounds control how much time the evolving solution set of a random formula spends in states that are about to be killed.
--
--   **Formalization Note** The schedule is a decidable predicate `ordinary : ℕ → Prop` together with `mask : ℕ → Finset (Assignment u)`; $P_i$ is `scheduledStep u k ordinary mask i`, $\mathcal M$ is `markovSum`, and $\Lambda$ is `lifetime u k`. The count of non-ordinary steps is the real sum over `i ∈ Finset.range L` of `if ordinary i then 0 else 1`. Averages over clauses are uniform averages `favg`, which are genuine expectations because $k\le u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/LifetimePotential.lean#L348-L367

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.scheduled_reward_integrated_critical {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    {Q Z : ℝ} (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * f S ≤ Q) {L : ℕ} (hL : 1 ≤ L)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S ≤ (Q+Z+1)*(1+Real.log L) := by sorry
