-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_theorem2_two_store
-- name    : MultiStoreAssort.SQR.theorem2_two_store
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:29.027975+00:00
-- url     : https://prove2.me/theorems/c56eab30-e941-41b4-b358-f9213a7bbf6c
-- title:
--   Theorem 2, PDF p. 15 — two stores, universally homogeneous discounts: a revenue-ordered optimum with S₂* ⊆ S̃ ⊆ S₁* (λ < 0.5) or S₁* ⊆ S̃ ⊆ S₂* (λ ≥ 0.5)
-- statement:
--   Consider the two-store SQR problem (5): a fraction $\lambda\in[0,1]$ of the customers visits store 1 and $1-\lambda$ visits store 2, and the objective is
--   $$
--   R(S_1,S_2)=\lambda\sum_{k}r_kp^Q_{1k}(S_1,S_2)+(1-\lambda)\sum_k r_kp^Q_{2k}(S_1,S_2).
--   $$
--   Suppose the utility discounts are universally homogeneous, $c_{12}^k=c_{21}^k=c>0$, and let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3), with $n\ge1$. Then there exists an optimal solution $(S_1^*,S_2^*)$ of (5) such that $S_1^*$ and $S_2^*$ are both revenue-ordered, and moreover
--   $$
--   S_2^*\subseteq\tilde S\subseteq S_1^*\ \text{ if } 0\le\lambda<0.5,\qquad S_1^*\subseteq\tilde S\subseteq S_2^*\ \text{ if } 0.5\le\lambda\le1 .
--   $$
--
--   The store with the higher demand runs a two-step selling process on a small assortment, while the lower-demand store carries a larger one.
--
--   **Formalization Note.** Problem (5) is the SQR objective `revQ` with two stores and weights $(\lambda,1-\lambda)$. One and the same optimal solution carries both properties. Revenues are positive and $r_1>\dots>r_n$, $v_k>0$, $c_{ii}^k=0$ as in §3.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 15, Theorem 2; problem (5) on PDF p. 14

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem theorem2_two_store {n : ℕ} (l : ℝ) (r v : Fin n → ℝ) (c : Fin 2 → Fin 2 → Fin n → ℝ)
    (c0 : ℝ) (hn : 0 < n) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0) (hu : UnivHomog c c0)
    (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin 2 → Finset (Fin n), IsOptQ ![l, 1 - l] r v c S ∧
      MultiStoreAssort.SMR.IsRevenueOrdered (S 0) ∧ MultiStoreAssort.SMR.IsRevenueOrdered (S 1) ∧
      (l < 1 / 2 → S 1 ⊆ St ∧ St ⊆ S 0) ∧ (1 / 2 ≤ l → S 0 ⊆ St ∧ St ⊆ S 1) := by sorry

end MultiStoreAssort.SQR
