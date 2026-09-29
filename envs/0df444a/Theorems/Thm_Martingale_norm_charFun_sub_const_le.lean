-- Prove2me | Theorems.Thm_Martingale_norm_charFun_sub_const_le
-- name    : Martingale.norm_charFun_sub_const_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:31:40.912559+00:00
-- url     : https://prove2.me/theorems/207cf8dc-889b-41cb-a50c-76350cd9b505
-- title:
--   McLeish's master inequality for the characteristic function of a bounded martingale difference sum
-- statement:
--   Let $(\mathcal{F}_k)_{k\in\mathbb{N}}$ be a filtration on a probability space $(\Omega,\mathcal{F},\mathbb{P})$ and let $(Z_k)_{k\in\mathbb{N}}$ be an adapted, integrable, uniformly bounded martingale difference sequence: $\mathbb{E}[Z_{k+1}\mid\mathcal{F}_k]=0$ a.s., $\mathbb{E}[Z_0]=0$, and $|Z_k|\le C$ everywhere. Fix $\theta, M\in\mathbb{R}$ and $n\in\mathbb{N}$, and suppose that along every path
--
--   * the squared variation is bounded: $\sum_{k<n} Z_k^2 \le M$, and
--   * the increments are small at scale $\theta$: $|\theta Z_k| \le 1$ for every $k<n$.
--
--   Then for **every** complex constant $c$, writing $S_n=\sum_{k<n}Z_k$,
--
--   $$\Bigl\| \mathbb{E}\bigl[e^{i\theta S_n}\bigr] - c \Bigr\| \;\le\; e^{\theta^2 M/2}\;\mathbb{E}\Bigl[\; \sum_{k<n}\bigl|\theta Z_k\bigr|^{3} \;+\; \Bigl| e^{-\frac{\theta^2}{2}\sum_{k<n} Z_k^2} - c \Bigr| \;\Bigr].$$
--
--   **What it does.** This is the single inequality that carries McLeish's argument from the algebraic decomposition to the central limit theorem. It bounds the distance between the characteristic function of $S_n$ and an *arbitrary* target constant $c$ by two explicitly controllable quantities: a third-moment term and the distance from the random Gaussian factor $\exp(-\tfrac{\theta^2}{2}\sum_{k<n}Z_k^2)$ to $c$.
--
--   Everything after this point is limit-taking with no further structure. Choosing $c = e^{-\theta^2\sigma^2/2}$:
--
--   * the third-moment term is dominated by $\bigl(\max_{k<n}|\theta Z_k|\bigr)\,\theta^2\sum_{k<n}Z_k^2 \le |\theta|^3 M \max_{k<n}|Z_k|$, which vanishes under the negligibility hypothesis;
--   * the second term vanishes whenever $\sum_{k<n}Z_k^2\to\sigma^2$, by continuity of $t\mapsto e^{-\theta^2 t/2}$ and bounded convergence.
--
--   Hence $\mathbb{E}[e^{i\theta S_n}]\to e^{-\theta^2\sigma^2/2}$ for every $\theta$, and Lévy's continuity theorem gives $S_n \Rightarrow \mathcal{N}(0,\sigma^2)$.
--
--   **Why an arbitrary constant $c$ is the right formulation.** The martingale property enters only through the exact identity $\mathbb{E}\bigl[\prod_{k<n}(1+i\theta Z_k)\bigr]=1$. Because the expectation is exactly $1$, subtracting a *constant* $c$ is the same as subtracting $c\prod_{k<n}(1+i\theta Z_k)$, and the difference factors as
--   $$e^{i\theta S_n} - c\prod_{k<n}(1+i\theta Z_k) \;=\; \underbrace{\prod_{k<n}(1+i\theta Z_k)}_{J^{(1)}_n}\cdot\Bigl(J^{(2)}_n - c\Bigr),\qquad J^{(2)}_n=\frac{e^{i\theta S_n}}{\prod_{k<n}(1+i\theta Z_k)} .$$
--   This step *fails for a random $c$*: one would be left with the extra term $\mathbb{E}[c\,(J^{(1)}_n-1)]$, which need not vanish. That is exactly why the random Gaussian factor cannot be used directly as the comparison object and must itself be compared to the constant $e^{-\theta^2\sigma^2/2}$ — the second term on the right-hand side.
--
--   **The role of $M$.** The prefactor $e^{\theta^2 M/2}$ is the uniform bound on $|J^{(1)}_n|$, coming from $|J^{(1)}_n|^2=\prod_{k<n}(1+\theta^2Z_k^2)\le e^{\theta^2\sum_{k<n}Z_k^2}\le e^{\theta^2 M}$. In McLeish's general theorem this pointwise bound is replaced by uniform integrability of $\{|J^{(1)}_n|\}$; the pathwise bound assumed here is the form in which the hypothesis is available in the applications (bounded or truncated arrays), and it keeps the estimate completely explicit.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.norm_charFun_sub_const_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (Z k))
    (hadapt : ∀ k, Measurable[ℱ k] (Z k))
    (hint : ∀ k, Integrable (Z k) P)
    (hmds : ∀ k, P[Z (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∫ ω, Z 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ k ω, |Z k ω| ≤ C)
    (θ M : ℝ) (n : ℕ)
    (hvar : ∀ ω, ∑ k ∈ Finset.range n, Z k ω ^ 2 ≤ M)
    (hsmall : ∀ k ∈ Finset.range n, ∀ ω, |θ * Z k ω| ≤ 1)
    (c : ℂ) :
    ‖(∫ ω, Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ)) ∂P) - c‖
      ≤ Real.exp (θ ^ 2 * M / 2) *
        ∫ ω, ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3)
          + ‖((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ) - c‖) ∂P := by sorry
