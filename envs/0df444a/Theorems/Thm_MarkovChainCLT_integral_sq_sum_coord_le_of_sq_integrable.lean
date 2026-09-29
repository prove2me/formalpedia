-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_sum_coord_le_of_sq_integrable
-- name    : MarkovChainCLT.integral_sq_sum_coord_le_of_sq_integrable
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:48:10.164454+00:00
-- url     : https://prove2.me/theorems/6d2a8151-faa4-44b9-987b-522b25000b47
-- title:
--   $O(n)$ partial-sum variance for square-integrable observables
-- statement:
--   **The $O(n)$ variance bound for partial sums, for square-integrable observables.** If the $N$-step kernel satisfies $\sup_x\|P^N(x,\cdot)-\pi\|\le\rho$ with $4\rho\le1/4$, then for **every** $r \in L^2(\pi)$ with $\mathbb E_\pi r = 0$ — no boundedness assumed —
--   $$\mathbb E_\pi\Bigl[\Bigl(\sum_{k<n} r(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4N\,n\,\|r\|_{L^2(\pi)}^2 .$$
--
--   **Removing boundedness is what makes this usable.** The underlying covariance estimate is proved through the conditional-expectation form of the Markov property, which is stated for bounded observables. But the intended application is precisely to an *unbounded* remainder: in the central limit theorem for a square-integrable $f$ one truncates, $f = f_K + r_K$, proves the theorem for the bounded part, and needs
--   $$\mathbb E_\pi\Bigl[\Bigl(\tfrac1{\sqrt n}\sum_{k<n}r_K(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4N\,\|r_K\|_{L^2(\pi)}^2 \qquad\text{uniformly in } n$$
--   for the unbounded remainder $r_K$, whose sup norm does not tend to zero even though its $L^2$ norm does.
--
--   **Proof.** Truncate: let $t_M = r\,\mathbf 1_{\{|r|\le M\}}$ and $u_M = t_M - \mathbb E_\pi t_M$, so each $u_M$ is bounded and centred and $u_M \to r$ pointwise (dominated convergence gives $\mathbb E_\pi t_M \to \mathbb E_\pi r = 0$). The bounded case applies to each $u_M$:
--   $$\mathbb E\Bigl[\Bigl(\sum_{k<n} u_M(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4Nn\,\|u_M\|_{L^2(\pi)}^2 .$$
--   On the right, $\|u_M\|_{L^2(\pi)}^2 \to \|r\|_{L^2(\pi)}^2$ by dominated convergence, with dominating function $2r^2 + 2(\mathbb E_\pi|r|)^2$. On the left, the integrands converge pointwise, so Fatou's lemma gives
--   $$\mathbb E\Bigl[\Bigl(\sum_{k<n} r(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; \liminf_M \mathbb E\Bigl[\Bigl(\sum_{k<n} u_M(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4Nn\,\|r\|_{L^2(\pi)}^2 .$$
--   Fatou also shows the left-hand side is finite, so the partial sum really is square-integrable. Note that no domination is needed on the left — which is essential, since a dominating function there would require exactly the kind of bound being proved.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971, Ch. 18; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_sum_coord_le_of_sq_integrable {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π)
    (hmean : ∫ x, r x ∂π = 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * n * ∫ x, (r x) ^ 2 ∂π := by sorry
