-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_eq_5_2
-- name    : NesterovRCD.Accelerated.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:56.607023+00:00
-- url     : https://prove2.me/theorems/1a44b472-afa4-4776-ad88-120c94120bbd
-- title:
--   (5.2) — $\gamma_k^2-\gamma_k/n=\beta_ka_k^2/b_k^2=(\beta_k\gamma_k/n)(1-\alpha_k)/\alpha_k$
-- statement:
--   Let $n\ge1$ and $0\le\sigma<n^2$, and let $a_k,b_k,\gamma_k,\alpha_k,\beta_k$ be the coefficients of the method ACDM$(x_0)$ (5.1). Then for every $k\ge0$ the parameters satisfy
--   $$\gamma_k^2-\frac{\gamma_k}{n}=\beta_k\frac{a_k^2}{b_k^2}=\frac{\beta_k\gamma_k}{n}\cdot\frac{1-\alpha_k}{\alpha_k}.$$
--
--   This identity is what makes the coefficients of $\|y_k-x_*\|_1^2$ and of $f(y_k)$ cancel in the one-step estimate of the proof of Theorem 6, and it is used again to derive the growth bound (5.5) for $a_k$.
--
--   **Formalization Note** The hypothesis $\sigma<n^2$ is implicit in the paper: $\alpha_k$ divides by $n^2-\sigma$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 15, (5.2)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem eq_5_2 (n : ℕ) (hn : 0 < n) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (k : ℕ) :
    acdmGamma n σ k ^ 2 - acdmGamma n σ k / n
        = acdmBeta n σ k * (acdmA n σ k ^ 2 / acdmB n σ k ^ 2) ∧
    acdmBeta n σ k * (acdmA n σ k ^ 2 / acdmB n σ k ^ 2)
        = acdmBeta n σ k * acdmGamma n σ k / n * ((1 - acdmAlpha n σ k) / acdmAlpha n σ k) := by sorry

end NesterovRCD.Accelerated
