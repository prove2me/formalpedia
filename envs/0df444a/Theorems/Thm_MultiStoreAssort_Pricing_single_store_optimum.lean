-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_single_store_optimum
-- name    : MultiStoreAssort.Pricing.single_store_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:10.226219+00:00
-- url     : https://prove2.me/theorems/dae39827-7f5c-4f0b-8433-6863df89e224
-- title:
--   §8.1, PDF p. 28 (Wang 2012) — the single-store problem (14) has optimal value θ*, attained by the full set at prices θ* + 1/βₖ
-- statement:
--   Let $\alpha_1,\dots,\alpha_n>0$ and $\beta_1,\dots,\beta_n>0$, and let $\theta^*$ solve $\theta^*=\sum_{k\in\mathcal N}e^{\hat\alpha_k-\beta_k\theta^*}$ with $\hat\alpha_k=\alpha_k-\log\beta_k-1$. Consider the single-store joint assortment and pricing problem (14) under the MNL model,
--   $$\max_{S\subseteq\mathcal N,\ (p_k)\in\mathbb R^n}\ \frac{\sum_{k\in S}p_k\exp(\alpha_k-\beta_kp_k)}{1+\sum_{k\in S}\exp(\alpha_k-\beta_kp_k)}.$$
--   Then:
--
--   1. for every assortment $S\subseteq\mathcal N$ and every real price vector $(p_k)$, the objective of (14) is at most $\theta^*$;
--   2. the full product set $S=\mathcal N$ with the constant adjusted markup prices $p_k=\theta^*+1/\beta_k$ attains $\theta^*$.
--
--   So offering every product at the prices $\theta^*+1/\beta_k$ is optimal for (14), and its optimal value is $\theta^*$. This is the multi-product MNL pricing theorem with heterogeneous price sensitivities that the paper cites (see, e.g., Wang 2012); it is the single-store bound used in the proof of Theorem 6.
--
--   **Formalization Note** Prices range over all of $\mathbb R$, as on the page. The optimum is stated as a universal upper bound plus attainment, not through a supremum.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 28, (14) and the sentence after it; Online Supplement App. E.1, PDF p. 47 ("the constructed solution in Theorem 6 is exactly the optimal solution to problem (14) for each store (see, e.g., Wang 2012)")

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem single_store_optimum {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (θ : ℝ) (hθ : IsTheta a b θ) :
    (∀ (S : Finset (Fin n)) (p : Fin n → ℝ), rev14 a b S p ≤ θ) ∧
      rev14 a b Finset.univ (fun k => θ + 1 / b k) = θ := by sorry

end MultiStoreAssort.Pricing
