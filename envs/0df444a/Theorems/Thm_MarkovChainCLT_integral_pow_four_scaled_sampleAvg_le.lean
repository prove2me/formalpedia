-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_pow_four_scaled_sampleAvg_le
-- name    : MarkovChainCLT.integral_pow_four_scaled_sampleAvg_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T19:44:31.618312+00:00
-- url     : https://prove2.me/theorems/f9ea755e-4c51-4fd5-ba81-77d103e42f76
-- title:
--   Uniform fourth moment of the CLT-scaled sample average (bounded observable)
-- statement:
--   **A uniform fourth-moment bound for the CLT-scaled sample average of a bounded observable.**
--
--   Let $P$ be a Markov kernel with invariant probability $\pi$, uniformly ergodic, and let $f$ be measurable and bounded. Write $Y_n=\sqrt n\,(\bar f_n-\mathbb E_\pi f)$ for the central-limit-scaled sample average along the stationary chain. Then $Y_n$ is fourth-power integrable for every $n$, and
--   $$\sup_{n}\ \mathbb E\big[Y_n^4\big]\;<\;\infty .$$
--
--   This is the fourth-moment companion of the platform's `integral_sq_scaled_sampleAvg_le`, which bounds $\mathbb E[Y_n^2]$ uniformly. Equivalently, in terms of the unnormalised partial sums $S_n=\sum_{i\le n}(f(X_i)-\mathbb E_\pi f)$, the assertion is the classical $\mathbb E[S_n^4]=O(n^2)$ for a bounded observable of a geometrically mixing stationary chain.
--
--   **Why it is wanted.** A uniform second-moment bound alone does not make $\{Y_n^2\}$ uniformly integrable, and uniform integrability is exactly what is missing when one wants to conclude that the Gaussian limit in the Markov chain central limit theorem carries the *full* asymptotic variance rather than only part of it. With this bound the conclusion is immediate: for $\varphi_T(z)=\min(z^2,T^2)$ one has $z^2-\varphi_T(z)\le z^4/T^2$, so $\mathbb E[Y_n^2]\le\mathbb E[\varphi_T(Y_n)]+C/T^2$ uniformly in $n$, and letting $n\to\infty$ and then $T\to\infty$ pins the limit variance.
--
--   **Two standard routes.** Either directly, expanding $\mathbb E[S_n^4]=\sum_{i,j,k,l}\mathbb E[h(X_i)h(X_j)h(X_k)h(X_l)]$ and using the geometric decay of the mixing coefficients to show that only the $O(n^2)$ "paired" index patterns contribute; or through the martingale approximation, where uniform ergodicity solves the Poisson equation $f-\mathbb E_\pi f=\hat g-P\hat g$ with a *bounded* solution (`poissonEquation_of_bounded_of_uniformlyErgodic`), so that $S_n$ is a martingale with bounded increments up to an $O(1)$ boundary term, and a martingale with increments bounded by $c$ satisfies $\mathbb E[M_n^4]\le 3c^4n^2$ by the usual expansion in which every term with a unique maximal index vanishes.
--
--   Proving this closes the identification of the limit variance for bounded observables, and with it — through the truncation reduction already on the platform — the Markov chain central limit theorem with identified asymptotic variance, the delta method for chain statistics, and Theorem 9 of arXiv:2407.19618.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), Section 3 (uniform integrability in the CLT for uniformly ergodic chains); the fourth-moment bound E[S_n^4] = O(n^2) for bounded observables of geometrically mixing stationary sequences is classical, see e.g. E. Rio, Asymptotic Theory of Weakly Dependent Random Processes, Theorem 2.5, or the martingale route via Ibragimov's inequality for martingales with bounded increments. Fourth-moment companion of the platform's MarkovChainCLT.integral_sq_scaled_sampleAvg_le.

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem MarkovChainCLT.integral_pow_four_scaled_sampleAvg_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      Integrable (fun ω : ℕ → X =>
        (Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π)) ^ 4)
        (MarkovChainCLT.chainMeasure P π)
      ∧ ∫ ω, (Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π)) ^ 4
          ∂(MarkovChainCLT.chainMeasure P π) ≤ C := by sorry
