-- Prove2me | Theorems.Thm_OAI_RandomKSAT_capped_variance_upper
-- name    : OAI.RandomKSAT.capped_variance_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:18:56.278339+00:00
-- url     : https://prove2.me/theorems/2563ee40-2064-464b-b381-51078501efaf
-- title:
--   Variance of the capped random $k$-SAT failure time is $O(n\,\ell(k,n))$
-- statement:
--   For integers $k\ge 3$ and $n\ge k$ we use the following notions. A *clause* of width $k$ on the variables $[n]=\{0,1,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a $k$-element set $V\subseteq[n]$ (the *support* of $c$) and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $x:[n]\to\{\mathrm T,\mathrm F\}$ *satisfies* $c$ if $x(v)=\beta(v)$ for at least one $v\in V$. Let $\mathbb P_{n,k}$ be the law of a clause stream $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of independent clauses, each uniformly distributed over the $\binom nk2^k$ clauses of width $k$ on $[n]$. The *first failure time* of $\omega$ is
--   $F(\omega)=\min\{m\in\mathbb N:\ \omega_0,\dots,\omega_{m-1}\text{ have no common satisfying assignment}\}\in\mathbb N\cup\{\infty\}$, and for a real number $B>0$ the *capped failure time* is
--   $$
--   T_B(\omega)=\min\big(F(\omega),\lfloor Bn\rfloor\big).
--   $$
--   Finally let $\ell(k,n)=\log(en)=1+\log n$ if $k=3$ and $\ell(k,n)=1$ if $k\ge4$.
--
--   **Theorem.** For every integer $k\ge3$ and every real $B>0$ there is a constant $C\ge0$, depending only on $k$ and $B$, such that
--   $$
--   \operatorname{Var}_{\mathbb P_{n,k}}(T_B)\le C\,n\,\ell(k,n)\qquad\text{for all integers } n\ge k.
--   $$
--
--   Thus the standard deviation of the capped failure time is $O(\sqrt n)$ for $k\ge4$ and $O(\sqrt{n\log n})$ for $k=3$. This is the variance upper bound for the capped failure time in the variance theorem for random $k$-SAT clause streams; applied with the cap $B=U(k)=\log 2/(-\log(1-2^{-k}))$ and combined with a comparison between capped and uncapped failure times, it also gives the upper bound for the variance of the uncapped failure time.
--
--   **Formalization Note** In Lean $T_B$ is `T B`, the real number obtained from `min (firstFailure ω) (cap n B)` with `cap n B = ⌊B * n⌋₊`; the variance is Mathlib's `ProbabilityTheory.variance` under `streamLaw n k`, the infinite product of uniform clause laws; and `ell k n` is `Real.log (Real.exp 1 * n)` if `k = 3` and `1` otherwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/CappedUpper.lean#L75-L113

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.capped_variance_upper (k : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C*n*ell k n := by sorry
