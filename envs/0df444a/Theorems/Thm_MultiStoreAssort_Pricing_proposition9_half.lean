-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_proposition9_half
-- name    : MultiStoreAssort.Pricing.proposition9_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:30.970034+00:00
-- url     : https://prove2.me/theorems/624bd807-3177-4957-8154-93e7370a33e6
-- title:
--   Proposition 9, PDF p. 29 — the SMR optimum of Theorem 6 earns at least half the optimal revenue of the SQR joint problem (15)
-- statement:
--   In the setting of Theorem 6 ($\lambda_i\ge0$, $\sum_i\lambda_i=1$, $\alpha_{ik}>0$, $\beta_{ik}>0$, $c^k_{ij}\ge0$, $c^k_{ii}=0$, and $\theta^*_i$ the solution of the markup equation), consider the joint problem under sequential recommendation, whose objective is $R^Q(\mathbf S,\mathbf P)$ of (15): a store-$i$ customer first sees $S_i$, and only if she buys nothing is she shown $\bar S\setminus S_i$.
--
--   **Proposition 9.** The optimal solution $(\mathbf S^*,\mathbf P^*)$ of problem (13) from Theorem 6, namely $S^*_i=\mathcal N$ and $p^*_{ik}=\theta^*_i+1/\beta_{ik}$, achieves at least half of the optimal revenue of (15): for every profile $\mathbf S$, every real price matrix $\mathbf P$ and every best-store rule $l$,
--   $$R^Q(\mathbf S,\mathbf P)\ \le\ 2\,R^Q(\mathbf S^*,\mathbf P^*).$$
--
--   The single-store optimal solution is therefore a $\tfrac12$-approximation for the joint assortment and pricing problem under sequential recommendation, extending Proposition 7 of the paper to endogenous prices.
--
--   **Formalization Note** "The optimal solution to problem (13)" is read as the solution constructed in Theorem 6 (the proof in App. E.2 bounds the optimal value of (15) by twice $\sum_i\lambda_i\theta^*_i$, which is what that solution earns in (15)). "The optimal revenue in (15)" is expressed as a bound over all profiles, real prices and tie-breaking rules, not through a supremum.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 29, Proposition 9; proof Online Supplement App. E.2, PDF p. 48

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem proposition9_half {m n : ℕ} (lam : Fin m → ℝ) (α β : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hα : ∀ i k, 0 < α i k) (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (hcii : ∀ i k, c i i k = 0) (θ : Fin m → ℝ) (hθ : ∀ i, IsTheta (α i) (β i) (θ i)) :
    ∀ (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l l' : Fin m → Fin n → Fin m),
      IsBestStore α β c P S l →
        rev15 lam α β c S P l ≤
          2 * rev15 lam α β c (fun _ => Finset.univ) (fun i k => θ i + 1 / β i k) l' := by sorry

end MultiStoreAssort.Pricing
