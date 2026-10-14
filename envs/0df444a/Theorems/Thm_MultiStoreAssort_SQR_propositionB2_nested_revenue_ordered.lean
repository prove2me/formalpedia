-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_propositionB2_nested_revenue_ordered
-- name    : MultiStoreAssort.SQR.propositionB2_nested_revenue_ordered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:54.478322+00:00
-- url     : https://prove2.me/theorems/bdaf5d39-9ea4-4618-9d80-df37cb285745
-- title:
--   Proposition B.2, PDF p. 35 — with λₘ minimal and c₁ ≤ ⋯ ≤ cₘ, some optimal SQR solution is nested and all revenue-ordered
-- statement:
--   Consider the SQR problem with $m\ge2$ stores, $n\ge1$ products and store-wise homogeneous utility discounts $c_{ij}^k=c_i>0$ ($i\ne j$). Assume
--   $$
--   \lambda_m=\min\{\lambda_1,\dots,\lambda_m\}\qquad\text{and}\qquad c_1\le c_2\le\dots\le c_m .
--   $$
--   Then there exists an optimal solution $(S_1^*,\dots,S_m^*)$ of the SQR problem such that $S_1^*\subseteq S_2^*\subseteq\dots\subseteq S_m^*$ and every $S_i^*$ is revenue-ordered, i.e. of the form $\{1,\dots,k_i\}$ with $k_i\in[n]$.
--
--   This completes Step 2 of the proof of Theorem 4.
--
--   **Formalization Note.** Revenue-ordered sets are nonempty (as on p. 11), so $n\ge 1$ is assumed. Stores are `Fin (M+2)`. The standing assumptions of §3 are hypotheses, revenues are positive. The paper's proof sketches its final iteration ("If we continue the analysis, one can show…"); the statement is posed as printed.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 35, Proposition B.2 (proof PDF pp. 39–42)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem propositionB2_nested_revenue_ordered {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧ (∀ i j, i ≤ j → S i ⊆ S j) ∧
      ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i) := by sorry

end MultiStoreAssort.SQR
