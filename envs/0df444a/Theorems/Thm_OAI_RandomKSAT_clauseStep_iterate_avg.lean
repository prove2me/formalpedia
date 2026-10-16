-- Prove2me | Theorems.Thm_OAI_RandomKSAT_clauseStep_iterate_avg
-- name    : OAI.RandomKSAT.clauseStep_iterate_avg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:19:15.854397+00:00
-- url     : https://prove2.me/theorems/a4d062d1-048e-4840-a0e0-25129075f9f7
-- title:
--   Iterating the one-clause averaging operator equals averaging over tuples of clauses
-- statement:
--   Let $u,s,m\in\mathbb N$. Assignments are maps $a:[u]\to\{\mathrm T,\mathrm F\}$ on $[u]=\{0,\dots,u-1\}$; a clause of width $s$ is a pair $c=(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, and $a$ satisfies $c$ if $a(v)=\beta(v)$ for some $v\in V$. Let $\mathcal C_{u,s}$ be the finite set of width-$s$ clauses and $\operatorname{Sat}(c)$ the set of assignments satisfying $c$. For a finite set $X$ and $h:X\to\mathbb{R}$ write $\mathbb E_{x\in X}[h(x)]=\frac1{|X|}\sum_{x\in X}h(x)$ for the uniform average. The *clause-step operator* acts on functions $f$ from finite sets of assignments to $\mathbb{R}$ by
--   $$
--   (P_sf)(S)=\mathbb E_{c\in\mathcal C_{u,s}}\big[f(S\cap\operatorname{Sat}(c))\big],
--   $$
--   and for a tuple $\mathbf c=(c_0,\dots,c_{m-1})$ of clauses the residual set is $S\langle\mathbf c\rangle=\{a\in S: a \text{ satisfies every } c_i\}$.
--
--   **Theorem.** For every function $f$ from finite sets of assignments to $\mathbb{R}$ and every finite set $S$ of assignments,
--   $$
--   (P_s^{\,m}f)(S)=\mathbb E_{\mathbf c\in\mathcal C_{u,s}^{\,m}}\big[f(S\langle\mathbf c\rangle)\big].
--   $$
--
--   The operator $P_s$ is the transition operator of the Markov chain that filters a solution set by one fresh uniformly random clause at a time. The identity says that $m$ steps of this chain amount to filtering $S$ by $m$ independent uniform clauses at once, so quantities defined through the chain can be computed as averages over formulas with $m$ clauses.
--
--   **Formalization Note** $P_s^{\,m}$ is the $m$-fold iterate `(clauseStep u s)^[m]`, the average is `favg`, and $\mathcal C_{u,s}^{\,m}$ is the function type `Fin m -> Clause u s`. No hypothesis $s\le u$ is needed: if $s>u$ there are no clauses, and for $m\ge1$ both sides are $0$ by the convention that an average over an empty set (a division by $0$) is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/MarkovReplacement.lean#L117-L130

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.clauseStep_iterate_avg (u s m : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) :
    (clauseStep u s)^[m] f S = favg (fun cs : Fin m → Clause u s => f (residual S cs)) := by sorry
