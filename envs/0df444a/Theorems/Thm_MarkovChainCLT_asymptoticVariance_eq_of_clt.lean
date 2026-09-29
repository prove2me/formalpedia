-- Prove2me | Theorems.Thm_MarkovChainCLT_asymptoticVariance_eq_of_clt
-- name    : MarkovChainCLT.asymptoticVariance_eq_of_clt
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-21T17:25:57.347507+00:00
-- url     : https://prove2.me/theorems/06cb015d-81f8-4433-a983-f1d1fb946ed6
-- title:
--   The Markov chain CLT limit variance is the autocovariance series
-- statement:
--   **Identification of the limit variance in the Markov chain CLT.**
--
--   Let $P$ be a Markov transition kernel on a measurable state space $\mathsf X$ with invariant probability $\pi$, and suppose the chain is Harris ergodic and *uniformly* ergodic, i.e. $\|P^n(x,\cdot)-\pi\|\le R\,t^n$ for some $R\ge 0$ and $t<1$, uniformly in the starting point. Let $f$ be measurable with $\mathbb E_\pi f^2<\infty$, and write
--   $$\bar f_n \;=\; \frac1n\sum_{i=1}^n f(X_i),\qquad \sigma^2(f)\;=\;\operatorname{Var}_\pi\!\big(f(X_0)\big)\;+\;2\sum_{k\ge 1}\operatorname{Cov}_\pi\!\big(f(X_0),f(X_k)\big).$$
--
--   Under these hypotheses the central limit theorem $\sqrt n\,(\bar f_n-\mathbb E_\pi f)\Rightarrow N(0,v)$ is already available (Ibragimov--Linnik 1971; Tierney 1994; Jones 2004, Corollary 5), but it produces the limit variance $v$ only as an unidentified constant. This statement supplies the missing identification: **whenever the chain started from stationarity satisfies such a central limit theorem with limit law $N(0,v)$, the constant $v$ is exactly the autocovariance series $\sigma^2(f)$.**
--
--   The series converges absolutely under these hypotheses --- uniform ergodicity makes the transition operator a strict $L^2(\pi)$ contraction on mean-zero functions after finitely many steps, so $|\operatorname{Cov}_\pi(f(X_0),f(X_k))|$ decays geometrically --- so $\sigma^2(f)$ is a well-defined real number and the assertion is an identity between two finite quantities. Since a sequence of random variables has at most one limit law and $v\mapsto N(0,v)$ is injective, $v$ is already determined by the chain and by $f$; the content here is that the determined value is the classical autocovariance expression and not some smaller constant.
--
--   Equivalently: $n\operatorname{Var}(\bar f_n)\to\sigma^2(f)$, *and* no mass escapes in the limit, so the limiting Gaussian carries the full asymptotic variance. This is the scalar form of the variance identification in the multivariate Markov chain central limit theorem that underlies the asymptotic theory of Markov chain Monte Carlo and of Markovian A/B experiments. Combined with the published central limit theorem it yields the sharpened form in which the asymptotic variance is displayed explicitly.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), Section 1 eq. (1) and Section 3 (identification of the asymptotic variance sigma_f^2 as the autocovariance series); the existence of the limit variance is Corollary 5 there (Ibragimov-Linnik 1971; Tierney 1994). See also Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, Appendix EC.3, Lemma EC.4 (multivariate form, citing Vats 2017).

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem MarkovChainCLT.asymptoticVariance_eq_of_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0 v)) :
    (v : ℝ) = MarkovChainCLT.asymptoticVariance P π f := by sorry
