-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_sum_mds_le
-- name    : MarkovChainCLT.integral_sq_sum_mds_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:21:11.070079+00:00
-- url     : https://prove2.me/theorems/235443ec-ea48-4c85-97a0-93b2bb2c0a36
-- title:
--   Orthogonality gives a linear variance bound for the chain's martingale differences
-- statement:
--   **A linear-in-$n$ variance bound for the martingale differences of a Markov chain.** For a bounded measurable $g$ put
--   $$D_k \;=\; g(X_{k+1}) - (Pg)(X_k), \qquad (Pg)(x) = \int g\,dP(x,\cdot).$$
--   Then, under the chain law from **any** initial distribution,
--   $$\mathbb E\Bigl[\Bigl(\sum_{k<n} D_k\Bigr)^{\!2}\Bigr] \;\le\; n\,(2\|g\|_\infty)^2 .$$
--
--   **Why the bound is linear and not quadratic.** A priori a sum of $n$ variables each bounded by $2\|g\|_\infty$ only gives $n^2(2\|g\|_\infty)^2$. The gain of a whole factor of $n$ comes from **orthogonality**: by the Markov property, $\mathbb E[D_k \mid \sigma(X_0,\dots,X_k)] = (Pg)(X_k) - (Pg)(X_k) = 0$, so for $j<k$ the pull-out property of conditional expectation gives
--   $$\mathbb E[D_jD_k] \;=\; \mathbb E\bigl[D_j\,\mathbb E[D_k\mid \sigma(X_0,\dots,X_k)]\bigr] \;=\; 0,$$
--   since $D_j$ is measurable with respect to $\sigma(X_0,\dots,X_k)$ whenever $j+1\le k$. Expanding the square therefore leaves only the diagonal, $\sum_{k<n}\mathbb E D_k^2 \le n(2\|g\|_\infty)^2$.
--
--   **What it is used for.** This is the workhorse behind the law of large numbers for a uniformly ergodic chain. Applying it to a solution $g$ of the Poisson equation $g - Pg = \varphi - \mathbb E_\pi\varphi$ turns the partial sums of $\varphi$ into a martingale plus a bounded remainder and yields
--   $$\mathbb E\Bigl[\Bigl(\tfrac1n\sum_{k<n}\varphi(X_k) - \mathbb E_\pi\varphi\Bigr)^{\!2}\Bigr] \;=\; O(1/n),$$
--   i.e. convergence in $L^2$ — hence in probability — with no ergodic theorem needed. In the central limit theorem it is what makes the quadratic variation $\frac1n\sum_{k<n}D_k^2$ converge to its mean, which is the last hypothesis of the martingale CLT. The bound holds for every initial law, not only the stationary one.
-- source:
--   M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Section 3.3; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_sum_mds_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, (g (ω (k + 1)) - ∫ y, g y ∂(P (ω k)))) ^ 2
        ∂(chainMeasure P lam)
      ≤ n * (2 * C) ^ 2 := by sorry
