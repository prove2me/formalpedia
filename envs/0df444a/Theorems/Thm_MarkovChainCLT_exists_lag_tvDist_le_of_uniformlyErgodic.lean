-- Prove2me | Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
-- name    : MarkovChainCLT.exists_lag_tvDist_le_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:22:27.783565+00:00
-- url     : https://prove2.me/theorems/a37b4fbf-f0ab-41a0-a794-34f8bb0592a6
-- title:
--   A uniformly ergodic chain has a uniform contraction lag
-- statement:
--   **Uniform ergodicity yields a fixed lag at which the chain has already contracted.** If $P$ is uniformly ergodic with respect to $\pi$, there is an $N \ge 1$ with
--   $$\sup_x \; \bigl\| P^N(x, \cdot) - \pi \bigr\|_{TV} \;\le\; \tfrac1{16}.$$
--
--   The constant $1/16$ is not special; it is the threshold at which the $L^2$ operator bound $\|P^N r\|_{L^2(\pi)} \le \tfrac12 \|r\|_{L^2(\pi)}$ becomes available for centred $r$, which is what drives the geometric decay of autocovariances and hence the $O(n)$ bound on the variance of partial sums. Extracting such an $N$ is the first step of essentially every quantitative argument for uniformly ergodic chains.
--
--   **Proof.** Uniform ergodicity provides constants $R \ge 0$ and $t \in [0,1)$ with $\|P^n(x,\cdot) - \pi\|_{TV} \le R t^n$ for all $x$ and all $n \ge 1$. Since $t < 1$, $R t^n \to 0$, so eventually $R t^n \le 1/16$; take any such $n$ that is also at least $1$.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, Springer 1993, Theorem 16.0.2; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.exists_lag_tvDist_le_of_uniformlyErgodic {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (huni : UniformlyErgodic P π) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16 := by sorry
