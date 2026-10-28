-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_theorem3_univ_homog
-- name    : MultiStoreAssort.SQR.theorem3_univ_homog
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:38.83514+00:00
-- url     : https://prove2.me/theorems/f5a4e7c7-feaf-4bf4-872d-553681a880d2
-- title:
--   Theorem 3, PDF p. 16 — with universally homogeneous discounts and λₘ minimal, some optimal SQR solution has S₁* = ⋯ = Sₘ₋₁* ⊆ S̃ ⊆ Sₘ*
-- statement:
--   Consider the SQR problem with $m\ge2$ stores and $n\ge1$ products, and suppose the utility discounts are universally homogeneous: $c_{ij}^k=c$ with $c>0$ for all $i\ne j$ and all $k$. Assume $\lambda_m=\min\{\lambda_1,\dots,\lambda_m\}$, and let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3). Then there exists an optimal solution $(S_1^*,\dots,S_m^*)$ of the SQR problem such that
--   $$
--   S_1^*=S_2^*=\dots=S_{m-1}^*\subseteq\tilde S\subseteq S_m^*
--   $$
--   and $S_1^*$ and $S_m^*$ are both revenue-ordered.
--
--   With a common discount the first $m-1$ stores can share one assortment, and the low-demand store $m$ carries the widest assortment.
--
--   **Formalization Note.** Stores are `Fin (M+2)` ($m\ge2$); revenue-ordered sets are nonempty, so $n\ge1$; revenues are positive; the remaining hypotheses are the standing assumptions of §3.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 16, Theorem 3 (proof Online Supplement App. B.2, PDF pp. 34–35)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem theorem3_univ_homog {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (c0 : ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hu : UnivHomog c c0) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      (∀ i, i ≠ Fin.last (M + 1) → S i = S 0) ∧ S 0 ⊆ St ∧ St ⊆ S (Fin.last (M + 1)) ∧
      MultiStoreAssort.SMR.IsRevenueOrdered (S 0) ∧ MultiStoreAssort.SMR.IsRevenueOrdered (S (Fin.last (M + 1))) := by sorry

end MultiStoreAssort.SQR
