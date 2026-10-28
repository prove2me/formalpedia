-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_propositionB1_subset_last
-- name    : MultiStoreAssort.SQR.propositionB1_subset_last
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:13.074597+00:00
-- url     : https://prove2.me/theorems/0692c965-5769-404a-a803-1505b5b1dddd
-- title:
--   Proposition B.1, PDF p. 35 — with λₘ minimal and cₘ maximal, some optimal SQR solution has Sᵢ* ⊆ Sₘ* for every i
-- statement:
--   Consider the SQR problem with $m\ge 2$ stores and store-wise homogeneous utility discounts $c_{ij}^k=c_i>0$ ($i\ne j$). Assume that store $m$ has the smallest arrival fraction and the largest discount,
--   $$
--   \lambda_m=\min\{\lambda_1,\dots,\lambda_m\},\qquad c_m=\max\{c_1,\dots,c_m\}.
--   $$
--   Then there exists an optimal solution $(S_1^*,\dots,S_m^*)$ of the SQR problem such that
--   $$
--   S_i^*\subseteq S_m^*\qquad\text{for all } i=1,\dots,m-1.
--   $$
--
--   This is the first step of the proof of Theorem 4: the store with the lowest demand carries every product offered anywhere.
--
--   **Formalization Note.** Stores are `Fin (M+2)`, so $m=M+2\ge 2$ and store $m$ is the last index. The standing assumptions of §3 are hypotheses: $\lambda_i\ge 0$, $\sum_i\lambda_i=1$, $r_1>\dots>r_n$, $v_k>0$, $c_{ii}^k=0$; revenues are additionally assumed positive (prices).
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 35, Proposition B.1 (proof PDF pp. 36–37)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem propositionB1_subset_last {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmax : ∀ i, cs i ≤ cs (Fin.last (M + 1))) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      ∀ i, i ≠ Fin.last (M + 1) → S i ⊆ S (Fin.last (M + 1)) := by sorry

end MultiStoreAssort.SQR
