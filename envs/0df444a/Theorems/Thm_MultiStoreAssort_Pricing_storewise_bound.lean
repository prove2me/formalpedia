-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_storewise_bound
-- name    : MultiStoreAssort.Pricing.storewise_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:39.771774+00:00
-- url     : https://prove2.me/theorems/9971f315-b351-45b1-97c9-a6bdbc19c3cb
-- title:
--   App. E.1, PDF p. 47 — under SMR, each store's revenue is at most the single-store optimum θ*ᵢ
-- statement:
--   Consider the multistore joint pricing model under simultaneous recommendation, with $\alpha_{ik}>0$, $\beta_{ik}>0$, discounts $c^k_{ij}\ge 0$ and $c^k_{ii}=0$, and let $\theta^*_i$ solve $\theta^*_i=\sum_{k\in\mathcal N}e^{\hat\alpha_{ik}-\beta_{ik}\theta^*_i}$ with $\hat\alpha_{ik}=\alpha_{ik}-\log\beta_{ik}-1$. For every assortment profile $\mathbf S$, every real price matrix $\mathbf P$, every best-store rule $l$ for $(\mathbf S,\mathbf P)$ and every store $i$,
--   $$\frac{\sum_{k\in S_i}p_{ik}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde p_{ik}(\mathbf S)\tilde v_{ik}(\mathbf S)}{1+\sum_{k\in S_i}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde v_{ik}(\mathbf S)}\ \le\ \theta^*_i.$$
--
--   The expected revenue of store $i$ under (13) never exceeds the optimal value of the single-store problem (14) with that store's parameters. Summing with the weights $\lambda_i$ gives the upper bound in Theorem 6.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), Online Supplement App. E.1, proof of Theorem 6, PDF p. 47

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem storewise_bound {m n : ℕ} (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (hα : ∀ i k, 0 < α i k) (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (hcii : ∀ i k, c i i k = 0) (θ : Fin m → ℝ) (hθ : ∀ i, IsTheta (α i) (β i) (θ i))
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m)
    (hl : IsBestStore α β c P S l) (i : Fin m) :
    storeRev13 α β c S P l i ≤ θ i := by sorry

end MultiStoreAssort.Pricing
