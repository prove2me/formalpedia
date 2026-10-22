-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_theta_exists_unique
-- name    : MultiStoreAssort.Pricing.theta_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:54.218166+00:00
-- url     : https://prove2.me/theorems/4af7274a-82f4-4757-ba40-a76586abcd66
-- title:
--   §8.1, PDF p. 28 — the markup equation θ = Σₖ exp(α̂ₖ − βₖθ) has a unique solution
-- statement:
--   Let $\alpha_1,\dots,\alpha_n>0$ and $\beta_1,\dots,\beta_n>0$, and put $\hat\alpha_k=\alpha_k-\log\beta_k-1$. Then the equation
--   $$\theta=\sum_{k\in\mathcal N}e^{\hat\alpha_k-\beta_k\theta}$$
--   has exactly one real solution $\theta^*$.
--
--   The paper applies this store by store, with $\alpha_k=\alpha_{ik}$, $\beta_k=\beta_{ik}$, to define $\theta^*_i$. The solution is the optimal revenue of the single-store joint assortment and pricing problem (14), and $\theta^*_i+1/\beta_{ik}$ are the optimal prices of Theorem 6. Existence and uniqueness make the hypothesis "$\theta_i$ solves the markup equation" of the main theorem satisfiable and unambiguous.
--
--   **Formalization Note** The positivity of $\alpha_k$ is the page's $\alpha_k\in\mathbb R^+$ and is not needed for the conclusion; $\beta_k>0$ is needed for $\log\beta_k$.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 28, §8.1, sentence defining θ*ᵢ before Theorem 6

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem theta_exists_unique {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) :
    ∃! θ : ℝ, IsTheta a b θ := by sorry

end MultiStoreAssort.Pricing
