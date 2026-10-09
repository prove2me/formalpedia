-- Prove2me | Theorems.Thm_NonconvexAG_Smooth_lemma_1
-- name    : NonconvexAG.Smooth.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:45.692691+00:00
-- url     : https://prove2.me/theorems/182f7114-6dbf-4a41-a1ab-6688e0f2fdba
-- title:
--   Lemma 1 — θ_k ≤ (1−α_k)θ_{k−1} + η_k implies θ_k ≤ Γ_k Σ_{i≤k} η_i/Γ_i
-- statement:
--   Let $\{\alpha_k\}$ satisfy $\alpha_1=1$ and $\alpha_k\in(0,1)$ for $k\ge2$, and let $\Gamma_k$ be defined by (2.6): $\Gamma_1=1$, $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$. Let $\{\theta_k\}_{k\ge0}$ and $\{\eta_k\}_{k\ge1}$ be real sequences with
--   $$\theta_k\le(1-\alpha_k)\theta_{k-1}+\eta_k,\qquad k=1,2,\dots \tag{2.5}$$
--   Then for every $k\ge1$,
--   $$\theta_k\le\Gamma_k\sum_{i=1}^k\frac{\eta_i}{\Gamma_i}.$$
--
--   This unrolling of a damped linear recursion is used twice in the proof of Theorem 1: with equality, to express $x^{ag}_k-x_k$ through the past gradients, and with $\theta_k=\Psi(x^{ag}_k)-\Psi(x)$ to sum the one-step bound (2.23).
--
--   **Formalization Note** The sequences are functions `ℕ → ℝ`; $\theta_0$ is arbitrary (its coefficient $1-\alpha_1$ vanishes).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Lemma 1

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

namespace NonconvexAG.Smooth

/-- Lemma 1 (p. 4). -/
theorem lemma_1 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (h : ∀ k, 1 ≤ k → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → θ k ≤ Gamma α k * ∑ i ∈ Finset.Icc 1 k, η i / Gamma α i := by sorry

end NonconvexAG.Smooth
