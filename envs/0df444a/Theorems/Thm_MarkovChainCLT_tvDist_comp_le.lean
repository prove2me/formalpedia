-- Prove2me | Theorems.Thm_MarkovChainCLT_tvDist_comp_le
-- name    : MarkovChainCLT.tvDist_comp_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:53:21.992034+00:00
-- url     : https://prove2.me/theorems/9b627658-0b94-4dff-b164-b93f2065b29a
-- title:
--   Data processing: a Markov kernel does not increase total variation distance
-- statement:
--   Let $K$ be a Markov kernel from $\mathsf X$ to $\mathsf Y$ and let $\mu,\nu$ be probability measures on $\mathsf X$. Then
--
--   $$\bigl\|K\!\circ\!\mu \;-\; K\!\circ\!\nu\bigr\| \;\le\; \|\mu-\nu\|,$$
--
--   where $K\!\circ\!\mu = \int K(x,\cdot)\,\mathrm{d}\mu(x)$ is the law obtained by drawing a starting point from $\mu$ and then applying $K$.
--
--   **Data processing.** *Randomly transforming two distributions by the same mechanism cannot make them easier to tell apart.* Total variation distance is exactly the optimal error in distinguishing two distributions from one sample, and a Markov kernel is a randomized map, so this is the statement that post-processing cannot increase statistical distinguishability.
--
--   **Use for Markov chains.** This is the step that transports a convergence rate on the *state space* to a rate on *path space*. If $\|\lambda P^m - \pi\| \le \varepsilon$, then applying the trajectory kernel to both sides gives
--   $$\bigl\|\mathbb{P}_{\lambda P^m} - \mathbb{P}_\pi\bigr\| \;\le\; \varepsilon,$$
--   i.e. the entire future of the chain started from $\lambda$ and observed from time $m$ onwards is within $\varepsilon$, in total variation, of the stationary chain. For a uniformly ergodic chain $\varepsilon = Rt^m$ decays geometrically, and this is precisely what lets a central limit theorem proved for the *stationary* chain be transferred to an arbitrary initial distribution — the "for every initial distribution" clause in the Markov chain CLT.
--
--   Iterating $K$ also gives the classical monotonicity $\|\mu P^{n+1} - \nu P^{n+1}\| \le \|\mu P^n - \nu P^n\|$: the distance to stationarity never increases along the chain.
--
--   **Proof.** For a measurable $B \subseteq \mathsf Y$, the function $g(x) = K(x,B)$ takes values in $[0,1]$ and is measurable, and by definition of composition
--   $$(K\!\circ\!\mu)(B) = \int g \,\mathrm{d}\mu, \qquad (K\!\circ\!\nu)(B) = \int g\,\mathrm{d}\nu.$$
--   Hence $|(K\!\circ\!\mu)(B) - (K\!\circ\!\nu)(B)| = \bigl|\int g\,\mathrm{d}\mu - \int g\,\mathrm{d}\nu\bigr| \le \|\mu-\nu\|$, by the bound on differences of integrals of $[0,1]$-valued functions. Taking the supremum over $B$ finishes.
--
--   The essential point is that $g$ is a *function*, not an indicator: the total variation distance is defined by testing against sets, and the whole content of the argument is that it also controls tests against arbitrary $[0,1]$-valued functions.
-- source:
--   S. Kullback and R. A. Leibler, "On Information and Sufficiency", Ann. Math. Statist. 22 (1951) 79-86; D. A. Levin and Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Lemma 4.11 and Exercise 4.2; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728.

import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

theorem MarkovChainCLT.tvDist_comp_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤ tvDist μ ν := by sorry
