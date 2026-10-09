-- Prove2me | Theorems.Thm_NonconvexAG_Composite_lemma_1
-- name    : NonconvexAG.Composite.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:09.853981+00:00
-- url     : https://prove2.me/theorems/af883a27-7368-4918-a91e-e17e861bc319
-- title:
--   Lemma 1 — θ_k ≤ (1−α_k)θ_{k−1} + η_k implies θ_k ≤ Γ_k Σ_{i≤k} η_i/Γ_i
-- statement:
--   Let $\{\alpha_k\}$ be step sizes with $\alpha_1=1$ and $\alpha_k\in(0,1)$ for $k\ge2$, and let $\Gamma_k$ be defined by (2.6): $\Gamma_1=1$, $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$. If real sequences $\{\theta_k\}$, $\{\eta_k\}$ satisfy
--   $$\theta_k\le(1-\alpha_k)\theta_{k-1}+\eta_k,\qquad k=1,2,\dots,$$
--   then for every $k\ge1$
--   $$\theta_k\le\Gamma_k\sum_{i=1}^k\frac{\eta_i}{\Gamma_i}.$$
--
--   This unrolls the one-step recursion of the AG method into a weighted sum; in the proof of Theorem 2 it turns the one-step bound (2.51) into the summed bound after it.
--
--   **Formalization Note** Sequences are indexed by `ℕ`, and $\theta_0$ is arbitrary (at $k=1$ it is multiplied by $1-\alpha_1=0$). Restated from mission 1 of this series because drafts cannot import one another.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Lemma 1

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- Lemma 1 (p. 4). -/
theorem lemma_1 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (h : ∀ k, 1 ≤ k → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → θ k ≤ NonconvexAG.Smooth.Gamma α k * ∑ i ∈ Finset.Icc 1 k, η i / NonconvexAG.Smooth.Gamma α i := by sorry
end NonconvexAG.Composite
