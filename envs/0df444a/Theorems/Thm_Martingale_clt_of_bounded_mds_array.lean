-- Prove2me | Theorems.Thm_Martingale_clt_of_bounded_mds_array
-- name    : Martingale.clt_of_bounded_mds_array
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:44:49.65794+00:00
-- url     : https://prove2.me/theorems/4ecb59b9-0aa8-4669-bda1-1a6943b03df8
-- title:
--   The martingale central limit theorem for uniformly bounded arrays (Brown–McLeish)
-- statement:
--   Let $(\mathcal{F}_k)_{k\in\mathbb{N}}$ be a filtration on a probability space $(\Omega,\mathcal{F},\mathbb{P})$ and let $\bigl(D_{n,k}\bigr)_{n,k\in\mathbb{N}}$ be a triangular array which, for each fixed $n$, is an adapted, integrable martingale difference sequence: $\mathbb{E}[D_{n,k+1}\mid \mathcal{F}_k]=0$ a.s. and $\mathbb{E}[D_{n,0}]=0$. Suppose
--
--   1. **uniform negligibility**: $|D_{n,k}| \le C_n$ everywhere, with $C_n \to 0$;
--   2. **uniformly bounded squared variation**: $\sum_{k<n} D_{n,k}^2 \le M$ along every path;
--   3. **convergence of the squared variation in $L^1$**: $\mathbb{E}\Bigl|\sum_{k<n} D_{n,k}^2 - \sigma^2\Bigr| \to 0$.
--
--   Then
--
--   $$S_n \;=\; \sum_{k<n} D_{n,k} \;\Longrightarrow\; \mathcal{N}\bigl(0,\sigma^2\bigr).$$
--
--   **What this is.** This is the martingale central limit theorem in the bounded-array form — the theorem of Brown (1971) and McLeish (1974) that replaces independence by the martingale-difference property. Independence is not assumed anywhere: the summands may depend on the entire past in an essentially arbitrary way, provided each is conditionally centred given what came before. It is the engine behind central limit theorems for Markov chains (through the Poisson-equation/Gordin martingale approximation), for stochastic approximation and MCMC, and for a large part of asymptotic statistics, where score functions and estimating equations are naturally martingales rather than sums of independent terms.
--
--   **On the hypotheses.** The three assumptions are the pathwise-bounded specialisation of McLeish's conditions.
--
--   * Condition 1 is the negligibility of individual increments. Without it a single summand could carry a non-vanishing share of the total and the limit would fail to be Gaussian. Here it is imposed in the strong uniform form $\sup_{k,\omega}|D_{n,k}| \le C_n \to 0$, which is what truncation arguments deliver in practice.
--   * Condition 2 replaces McLeish's uniform integrability of $\bigl\{\prod_{k<n}|1+i\theta D_{n,k}|\bigr\}$. It is what makes the comparison factor $J^{(1)}_n = \prod_{k<n}(1+i\theta D_{n,k})$ uniformly bounded, by $|J^{(1)}_n|^2 = \prod_{k<n}(1+\theta^2 D_{n,k}^2) \le e^{\theta^2 M}$.
--   * Condition 3 is the identification of the limiting variance. It is stated in $L^1$; combined with condition 2 this is equivalent to convergence in probability, since the integrands are uniformly bounded by $M + \sigma^2$.
--
--   No sign condition on $\sigma$ is required — only $\sigma^2$ enters, and the degenerate case $\sigma = 0$ is allowed, where the conclusion is convergence in probability to $0$.
--
--   **Proof.** By Lévy's continuity theorem it suffices to show $\mathbb{E}[e^{i\theta S_n}] \to e^{-\theta^2\sigma^2/2}$ for each fixed $\theta$. McLeish's master inequality, applied with the constant $c = e^{-\theta^2\sigma^2/2}$, bounds
--   $$\bigl\|\mathbb{E}[e^{i\theta S_n}] - c\bigr\| \;\le\; e^{\theta^2M/2}\,\mathbb{E}\Bigl[\sum_{k<n}|\theta D_{n,k}|^{3} + \bigl|e^{-\frac{\theta^2}{2}\sum_{k<n}D_{n,k}^2} - c\bigr|\Bigr],$$
--   valid as soon as $|\theta| C_n \le 1$, hence for all large $n$. The first term is at most $|\theta|^3 C_n M$, because $\sum_k |D_{n,k}|^3 \le \bigl(\max_k|D_{n,k}|\bigr)\sum_k D_{n,k}^2$, and vanishes by condition 1. The second is at most $\tfrac{\theta^2}{2}\,\mathbb{E}\bigl|\sum_{k<n}D_{n,k}^2 - \sigma^2\bigr|$, because $|e^{x}-e^{y}| \le |x-y|$ for $x,y \le 0$, and vanishes by condition 3. A squeeze argument on the eventual filter concludes.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.clt_of_bounded_mds_array {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (hadapt : ∀ n k, Measurable[ℱ k] (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hmds : ∀ n k, P[D n (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∀ n, ∫ ω, D n 0 ω ∂P = 0)
    (C : ℕ → ℝ) (hCbdd : ∀ n k ω, |D n k ω| ≤ C n)
    (hC0 : Tendsto C atTop (𝓝 0))
    (M : ℝ) (hM : ∀ n ω, ∑ k ∈ Finset.range n, D n k ω ^ 2 ≤ M)
    (σ : ℝ)
    (hvar : Tendsto (fun n : ℕ => ∫ ω, |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| ∂P)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (σ ^ 2).toNNReal) := by sorry
