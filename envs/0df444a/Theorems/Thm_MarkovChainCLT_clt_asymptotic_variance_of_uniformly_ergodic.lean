-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_asymptotic_variance_of_uniformly_ergodic
-- name    : MarkovChainCLT.clt_asymptotic_variance_of_uniformly_ergodic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T16:00:54.616461+00:00
-- url     : https://prove2.me/theorems/36b1bda1-bbc8-4514-9c70-b1fa5301aaf3
-- title:
--   Markov chain CLT with autocovariance-series variance (Lemma EC.4, scalar form)
-- statement:
--   Let $X = \{X_n\}$ be a Harris ergodic, **uniformly ergodic** Markov chain with kernel $P$ and stationary distribution $\pi$, and let $f$ be measurable with $E_\pi f^2 < \infty$. Then: (i) the autocovariance series $\sum_{k \ge 1} \mathrm{Cov}_\pi(f(X_0), f(X_k))$ is summable; (ii) the asymptotic variance $\sigma^2(f) = \mathrm{Var}_\pi(f) + 2\sum_{k\ge 1}\mathrm{Cov}_\pi(f(X_0), f(X_k))$ is nonnegative; and (iii) for **every** initial distribution, $\sqrt{n}\,(\bar f_n - E_\pi f) \xrightarrow{d} N(0, \sigma^2(f))$ where $\bar f_n = n^{-1}\sum_{i=1}^n f(X_i)$. This sharpens the platform's uniformly ergodic CLT (`MarkovChainCLT.clt_of_uniformly_ergodic`, which asserts existence of some asymptotic variance) by identifying the variance as the autocovariance series — the scalar form of the multivariate Markov chain CLT quoted as Lemma EC.4 of arXiv:2407.19618 (Vats 2017); the multivariate statement follows coordinatewise/directionally since the identified variance is a quadratic form in the observable.
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, Appendix EC.3, Lemma EC.4 (multivariate Markov chain CLT, citing Vats 2017), stated in scalar form with the asymptotic covariance identified

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem MarkovChainCLT.clt_asymptotic_variance_of_uniformly_ergodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    Summable (fun k : ℕ => MarkovChainCLT.lagCovariance P π f f (k + 1)) ∧
    0 ≤ MarkovChainCLT.asymptoticVariance P π f ∧
    ∀ (lam : Measure X) [IsProbabilityMeasure lam],
      TendstoInDistribution
        (fun (n : ℕ) (ω : ℕ → X) =>
          Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
        atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P lam)
        (gaussianReal 0 (MarkovChainCLT.asymptoticVariance P π f).toNNReal) := by sorry
