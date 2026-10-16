-- Prove2me | Theorems.Thm_OAI_RandomKSAT_hall_probability_bound
-- name    : OAI.RandomKSAT.hall_probability_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:20:55.408977+00:00
-- url     : https://prove2.me/theorems/da033144-b0a4-42fe-821d-54a15cf7c792
-- title:
--   Sparse random $k$-CNF formulas are unsatisfiable with probability at most $2a$
-- statement:
--   Let $k,n,m$ be natural numbers with $2\le k\le n$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. Let $w_0,\dots,w_{m-1}$ be independent random clauses, each uniformly distributed over the $\binom nk2^k$ clauses of width $k$ on $[n]$, and let $a\ge0$ be a real number with
--   $$
--   e^2a\le\tfrac12\qquad\text{and}\qquad m\le a\,n .
--   $$
--
--   **Theorem.** Under these hypotheses,
--   $$
--   \Pr\big[\text{no assignment } x:[n]\to\{\mathrm T,\mathrm F\}\text{ satisfies all of } w_0,\dots,w_{m-1}\big]\le 2a .
--   $$
--
--   So a random $k$-CNF formula whose clause density $m/n$ is at most a small constant $a$ is unsatisfiable with probability $O(a)$, uniformly in $n$. In the variance analysis of random $k$-SAT clause streams this bounds the probability that the first failure occurs within a small linear number of clauses.
--
--   **Formalization Note** The probability is the uniform average `favg` over all words `w : Fin m → Clause n k` of the indicator of `¬ finiteSAT w m`, where `finiteSAT w m` states that some assignment satisfies `w j` for every `j < m`, i.e. for every clause of the word.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/HallSatisfiability.lean#L181-L224

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.hall_probability_bound {n k m : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {a : ℝ} (ha : 0 ≤ a) (ha' : Real.exp 2*a ≤ 1/2) (hm : (m:ℝ) ≤ a*n) :
    favg (fun w : Fin m → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) ≤ 2*a := by sorry
