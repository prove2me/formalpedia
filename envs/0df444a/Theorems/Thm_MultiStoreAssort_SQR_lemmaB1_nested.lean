-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_lemmaB1_nested
-- name    : MultiStoreAssort.SQR.lemmaB1_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:08.579521+00:00
-- url     : https://prove2.me/theorems/d9140128-daae-4097-8660-4e1b28f6527b
-- title:
--   Lemma B.1, PDF p. 35 — with λₘ minimal and c₁ ≤ ⋯ ≤ cₘ, some optimal SQR solution is nested S₁* ⊆ ⋯ ⊆ Sₘ*
-- statement:
--   Consider the SQR problem with $m\ge2$ stores and store-wise homogeneous utility discounts $c_{ij}^k=c_i>0$ ($i\ne j$). Assume
--   $$
--   \lambda_m=\min\{\lambda_1,\dots,\lambda_m\}\qquad\text{and}\qquad c_1\le c_2\le\dots\le c_m .
--   $$
--   Then there exists an optimal solution $(S_1^*,\dots,S_m^*)$ of the SQR problem such that
--   $$
--   S_1^*\subseteq S_2^*\subseteq\dots\subseteq S_m^*.
--   $$
--
--   This completes Step 1 of the proof of Theorem 4.
--
--   **Formalization Note.** Stores are `Fin (M+2)` ($m\ge 2$); the nesting is $S_i\subseteq S_j$ for all store indices $i\le j$. The standing assumptions of §3 are hypotheses, and revenues are assumed positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 35, Lemma B.1 (proof PDF pp. 37–38)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem lemmaB1_nested {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧ ∀ i j, i ≤ j → S i ⊆ S j := by sorry

end MultiStoreAssort.SQR
