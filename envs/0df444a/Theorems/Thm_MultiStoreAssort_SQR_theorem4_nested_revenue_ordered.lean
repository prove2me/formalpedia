-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_theorem4_nested_revenue_ordered
-- name    : MultiStoreAssort.SQR.theorem4_nested_revenue_ordered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:29.635036+00:00
-- url     : https://prove2.me/theorems/64ead4d4-3126-466e-b82f-3edb750f8626
-- title:
--   Theorem 4, PDF p. 17 — with store-wise homogeneous discounts, λₘ minimal and c₁ ≤ ⋯ ≤ cₘ, some optimal SQR solution has S₁* ⊆ ⋯ ⊆ Sₘ₋₁* ⊆ S̃ ⊆ Sₘ*, all revenue-ordered
-- statement:
--   A seller runs $m\ge 2$ stores selling $n\ge1$ products with revenues $r_1>\dots>r_n>0$ and attraction values $v_k>0$. A fraction $\lambda_i\ge0$ of the customers visits store $i$ ($\sum_i\lambda_i=1$). Under sequential recommendation a customer of store $i$ first sees $S_i$ and, if she buys nothing, the products of $\bar S\setminus S_i$ with utility discount $c_i^k(\mathbf S)$; the expected revenue is
--   $$
--   R(\mathbf S)=\sum_{i=1}^m\lambda_i\sum_{k=1}^n r_k\,p^Q_{ik}(\mathbf S)
--   $$
--   with the choice probabilities (2). Suppose the utility discounts are store-wise homogeneous, $c_{ij}^k=c_i>0$ for $i\ne j$, and assume
--   $$
--   \lambda_m=\min\{\lambda_1,\dots,\lambda_m\}\qquad\text{and}\qquad c_1\le c_2\le\dots\le c_m .
--   $$
--   Let $\tilde S$ be the smallest revenue-ordered optimal assortment of the single-store problem (3). Then there exists an optimal solution $(S_1^*,\dots,S_m^*)$ of the SQR problem such that
--   $$
--   S_1^*\subseteq S_2^*\subseteq\dots\subseteq S_{m-1}^*\subseteq\tilde S\subseteq S_m^*
--   $$
--   and $S_1^*,\dots,S_m^*$ are all revenue-ordered.
--
--   The theorem says that the store with the least demand and the largest discount should carry the widest assortment, larger than the single-store optimum, while the other stores carry nested revenue-ordered assortments inside it; this reduces the search to nested prefixes.
--
--   **Formalization Note.** Stores are `Fin (M+2)` so that $m\ge2$ and stores $m-1$, $m$ are the last two indices. Revenue-ordered sets are nonempty prefixes $\{1,\dots,k\}$, $k\in[n]$, which needs $n\ge1$. Revenues are assumed positive (they are prices); the remaining hypotheses are the standing assumptions of §3. $\tilde S$ enters as a hypothesis `IsStilde r v St`, which is satisfiable (the milestone on p. 11).
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 17, Theorem 4; proof Online Supplement App. B.3–B.6, PDF pp. 35–43

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem theorem4_nested_revenue_ordered {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      (∀ i j, i ≤ j → j ≠ Fin.last (M + 1) → S i ⊆ S j) ∧
      S (Fin.last M).castSucc ⊆ St ∧ St ⊆ S (Fin.last (M + 1)) ∧
      ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i) := by sorry

end MultiStoreAssort.SQR
