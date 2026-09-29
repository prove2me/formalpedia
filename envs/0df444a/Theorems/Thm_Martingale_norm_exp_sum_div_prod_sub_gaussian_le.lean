-- Prove2me | Theorems.Thm_Martingale_norm_exp_sum_div_prod_sub_gaussian_le
-- name    : Martingale.norm_exp_sum_div_prod_sub_gaussian_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:25:36.379535+00:00
-- url     : https://prove2.me/theorems/59dfdde5-0101-46ac-b41d-ec9942f24ba2
-- title:
--   McLeish's factor $J^{(2)}$ is within $\sum_k|\theta Z_k|^3$ of the Gaussian factor
-- statement:
--   Let $Z_0, Z_1, \dots$ be real-valued functions on a set $\Omega$, let $\theta \in \mathbb{R}$, let $n \in \mathbb{N}$, and fix $\omega \in \Omega$. If $|\theta Z_k(\omega)| \le 1$ for every $k < n$, then
--
--   $$\left\| \frac{\exp\!\bigl(i\theta \sum_{k<n} Z_k(\omega)\bigr)}{\prod_{k<n}\bigl(1 + i\theta Z_k(\omega)\bigr)} \;-\; \exp\!\Bigl(-\tfrac{\theta^{2}}{2}\sum_{k<n} Z_k(\omega)^{2}\Bigr) \right\| \;\le\; \sum_{k<n} \bigl|\theta Z_k(\omega)\bigr|^{3}.$$
--
--   **What this is.** It is the deterministic, pathwise core of McLeish's proof of the martingale central limit theorem: the statement that the second factor in the decomposition
--   $$e^{i\theta S_n} \;=\; \underbrace{\prod_{k<n}\bigl(1 + i\theta Z_k\bigr)}_{J^{(1)}_n}\;\cdot\;\underbrace{\frac{e^{i\theta S_n}}{\prod_{k<n}(1 + i\theta Z_k)}}_{J^{(2)}_n}, \qquad S_n = \sum_{k<n} Z_k,$$
--   is uniformly close to the Gaussian factor $\exp\bigl(-\tfrac{\theta^2}{2}\sum_{k<n}Z_k^2\bigr)$, with an explicit cubic error.
--
--   No probability enters here at all — there is no measure, no filtration, no martingale hypothesis. That is the point of the decomposition: it cleanly separates the argument into a *probabilistic* half, where $\mathbb{E}\,J^{(1)}_n = 1$ follows from the martingale property alone, and this *analytic* half, which is a pathwise inequality about complex numbers.
--
--   **How the two hypotheses of the CLT are consumed.** The bound is useful exactly because of the shape of its right-hand side:
--   $$\sum_{k<n}|\theta Z_k|^{3} \;\le\; \Bigl(\max_{k<n}|\theta Z_k|\Bigr)\cdot \theta^{2}\sum_{k<n} Z_k^{2}.$$
--   Under the two standard hypotheses on a martingale-difference array — *negligibility* ($\max_{k<n}|Z_k| \to 0$ in probability) and *convergence of the squared variation* ($\sum_{k<n} Z_k^2 \to \sigma^2$ in probability) — the first factor vanishes and the second stays bounded, so the whole error tends to $0$. Simultaneously the Gaussian factor converges to the constant $e^{-\theta^2\sigma^2/2}$. Thus $J^{(2)}_n \to e^{-\theta^2\sigma^2/2}$, and combining with $\mathbb{E}\,J^{(1)}_n = 1$ yields $\mathbb{E}\,e^{i\theta S_n} \to e^{-\theta^2\sigma^2/2}$, which is the CLT by Lévy continuity.
--
--   **Proof.** Both sides factor over $k$: the quotient because $e^{i\theta\sum_k Z_k} = \prod_k e^{i\theta Z_k}$, and the Gaussian because $\exp(-\tfrac{\theta^2}{2}\sum_k Z_k^2) = \prod_k \exp(-\tfrac{(\theta Z_k)^2}{2})$. Each factor of the first product has modulus at most $1$, since $|e^{i\theta z}| = 1 \le |1 + i\theta z|$; each factor of the second lies in $(0,1]$. The elementary telescoping estimate $\bigl\|\prod_k a_k - \prod_k b_k\bigr\| \le \sum_k \|a_k - b_k\|$ for families bounded by $1$ then reduces the claim to the single-factor cubic bound $\bigl|e^{ix}/(1+ix) - e^{-x^2/2}\bigr| \le |x|^3$ at $x = \theta Z_k(\omega)$, which is where the hypothesis $|\theta Z_k(\omega)| \le 1$ is used.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset

theorem Martingale.norm_exp_sum_div_prod_sub_gaussian_le {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ)
    (n : ℕ) (ω : Ω) (hsmall : ∀ k ∈ Finset.range n, |θ * Z k ω| ≤ 1) :
    ‖Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ))
          / ∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))
        - ((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ)‖
      ≤ ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3 := by sorry
