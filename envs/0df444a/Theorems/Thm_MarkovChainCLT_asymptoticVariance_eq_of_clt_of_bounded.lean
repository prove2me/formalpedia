-- Prove2me | Theorems.Thm_MarkovChainCLT_asymptoticVariance_eq_of_clt_of_bounded
-- name    : MarkovChainCLT.asymptoticVariance_eq_of_clt_of_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T19:24:15.759139+00:00
-- url     : https://prove2.me/theorems/253b60b8-8cfb-4cec-9ac1-16b26bf2e71e
-- title:
--   The Markov chain CLT limit variance is the autocovariance series (bounded observable)
-- statement:
--   **The Markov chain CLT limit variance is the autocovariance series — bounded observable.**
--
--   Let $P$ be a Markov kernel with invariant probability $\pi$, Harris ergodic and uniformly ergodic, and let $f$ be measurable and **bounded**, $|f|\le B$. Write
--   $$\bar f_n=\frac1n\sum_{i=1}^n f(X_i),\qquad \sigma^2(f)=\operatorname{Var}_\pi\!\big(f(X_0)\big)+2\sum_{k\ge1}\operatorname{Cov}_\pi\!\big(f(X_0),f(X_k)\big).$$
--   If the stationary chain satisfies $\sqrt n(\bar f_n-\mathbb E_\pi f)\Rightarrow N(0,v)$, then $v=\sigma^2(f)$.
--
--   For a bounded observable the central limit theorem itself is already available on the platform (`clt_of_bounded_of_uniformlyErgodic`), so the entire content here is the *identification* of the constant it produces.
--
--   **Why the bounded case is the right place to attack this.** One inequality is cheap: $\mathbb E[(\sqrt n(\bar f_n-\mathbb E_\pi f))^2]$ is bounded uniformly in $n$ and converges to $\sigma^2(f)$, and weak convergence gives $v\le\sigma^2(f)$ by lower semicontinuity. The reverse inequality is exactly the statement that no mass escapes in the limit, and that needs uniform square-integrability of the CLT-scaled sums — which is where boundedness pays off. The classical route is the martingale approximation: uniform ergodicity solves the Poisson equation $f-\mathbb E_\pi f=\hat g-P\hat g$ with $\hat g$ *bounded* (`poissonEquation_of_bounded_of_uniformlyErgodic`), so
--   $$\sum_{i=1}^n\big(f(X_i)-\mathbb E_\pi f\big)=M_n+P\hat g(X_0)-P\hat g(X_n),$$
--   where $M_n$ is a martingale with bounded, stationary increments $D_i=\hat g(X_i)-P\hat g(X_{i-1})$ and the boundary term is $O(1)$, hence $o(\sqrt n)$ uniformly. Bounded increments give a fourth-moment bound $\mathbb E[M_n^4]=O(n^2)$, so $(M_n/\sqrt n)^2$ is uniformly integrable and $\mathbb E[(M_n/\sqrt n)^2]=\mathbb E[D_1^2]$ exactly, by orthogonality. Identifying $\mathbb E[D_1^2]=\mathbb E_\pi[\hat g^2]-\mathbb E_\pi[(P\hat g)^2]$ — the quantity already appearing in `integral_sq_quadVar_sub_le` — with $\sigma^2(f)$ is then a telescoping computation on the Poisson equation.
--
--   The unbounded $L^2$ case follows from this one by truncation and is separately available as a reduction, so proving this statement closes the Markov chain CLT with identified variance, and with it the delta method and Theorem 9 of arXiv:2407.19618.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), Section 1 eq. (1) and Section 3 (identification of the asymptotic variance as the autocovariance series), restricted to a bounded observable, where the CLT is Corollary 5 / Theorem 5 there. The martingale-approximation route is Section 3 of the same survey (Maxwell-Woodroofe; Kipnis-Varadhan). See also Chen, Simchi-Levi, Wang, https://arxiv.org/abs/2407.19618, Appendix EC.3, Lemma EC.4.

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem MarkovChainCLT.asymptoticVariance_eq_of_clt_of_bounded {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0 v)) :
    (v : ℝ) = MarkovChainCLT.asymptoticVariance P π f := by sorry
