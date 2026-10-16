-- Prove2me | Theorems.Thm_OAI_RandomKSAT_selected_variance
-- name    : OAI.RandomKSAT.selected_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:29:57.267257+00:00
-- url     : https://prove2.me/theorems/37729cde-d25c-4e90-86e8-8be4a2a96156
-- title:
--   Isolated clauses force variance of the failure time of a random clause word
-- statement:
--   Let $k,n,M,Q,V$ be natural numbers with $1\le k\le n$ and $Q+V\le M+1$. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. Let $w=(w_0,\dots,w_{M-1})$ be a word of $M$ independent clauses, each uniformly distributed over the $\binom nk2^k$ clauses of width $k$ on $[n]$. The *failure time* $\tau(w)$ is the least $m\le M$ such that $w_0,\dots,w_{m-1}$ have no common satisfying assignment, and $\tau(w)=M+1$ if all $M$ clauses are simultaneously satisfiable. An index $i$ is *isolated* in $w$ if the support of $w_i$ is disjoint from the supports of all $w_j$ with $j\ne i$; let $\mathrm{Iso}(w)$ be the set of isolated indices. Put
--   $$
--   p=\frac{Q\,(M+1-Q-V)}{(M+1)^2}\ \ge 0 .
--   $$
--
--   **Theorem.** Under these hypotheses,
--   $$
--   p\;\mathbb E\big[\min\big(Q,|\mathrm{Iso}(w)|\big)\big]\;\le\;\operatorname{Var}\big(\tau(w)\big)+p\,Q\,\Pr\big[\tau(w)<2Q\ \text{or}\ \tau(w)>V\big].
--   $$
--
--   Isolated clauses can be moved anywhere in the word without affecting satisfiability, and each of them, placed at a random position, shifts the failure time by a Bernoulli amount. The theorem turns this into a lower bound for the variance of the failure time: when the expected number of isolated clauses is of order $Q$ and the failure time falls in the window $[2Q,V]$ with high probability, $\operatorname{Var}(\tau(w))$ is of order $pQ$. With $M=2Rn$, $V=Rn$ and $Q$ a small multiple of $n$ this is of order $n$, which yields the linear lower bound for the variance of the random $k$-SAT failure time.
--
--   **Formalization Note** Expectations, probabilities and the variance are uniform averages over all words `w : Fin M → Clause n k` (`favg` and `fvariance`, the latter being the average of the square minus the square of the average). The failure time is `listStop (List.ofFn w)`, the probability is the average of `outsideWindow Q V`, and $\mathrm{Iso}(w)$ is `isolateSet w`. All arithmetic in $p$ is real, so $M+1-Q-V$ is an honest difference, nonnegative by hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderVariance.lean#L181-L212

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

theorem OAI.RandomKSAT.selected_variance {n k M : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Q V : ℕ) (hQV : Q+V ≤ M+1) :
    ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*
      favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card : ℝ)) ≤
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) +
      ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*Q*
        favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) := by sorry
