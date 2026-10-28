-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_step3_case2_add_product
-- name    : MultiStoreAssort.SQR.step3_case2_add_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:11.890289+00:00
-- url     : https://prove2.me/theorems/3cba6f9e-d3d3-4077-8ddd-e0272f327c1f
-- title:
--   Proof of Theorem 4, Step 3, Case 2, (B.9)–(B.10), PDF p. 43 — if S*ₘ ⊊ S̃, adding product |S*ₘ|+1 to store m does not decrease the revenue
-- statement:
--   Consider the SQR problem with $m\ge2$ stores, store-wise homogeneous discounts $c_{ij}^k=c_i>0$ with $c_1\le\dots\le c_m$, and $\lambda_m=\min_i\lambda_i$. Let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3). Let $(S_1,\dots,S_m)$ be a profile of revenue-ordered assortments in Case 2,
--   $$
--   S_1\subseteq S_2\subseteq\dots\subseteq S_{m-1}\subseteq S_m\subsetneq\tilde S,
--   $$
--   and let $j=|S_m|+1$ (so $j\in\tilde S$). Then
--   $$
--   R(S_1,\dots,S_{m-1},S_m\cup\{j\})\ \ge\ R(S_1,\dots,S_m).
--   $$
--
--   This is the conclusion drawn from (B.9) and (B.10) in Step 3 of the proof of Theorem 4; repeating it grows store $m$ up to $\tilde S$.
--
--   **Formalization Note.** The paper argues for the optimal solution of Proposition B.2; the inequality is stated for every revenue-ordered nested profile in Case 2. Products are 0-indexed, so product $|S_m|+1$ is the index $j$ with value $|S_m|$. The standing assumptions of §3 are hypotheses, revenues are positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 43, Appendix B.6, proof of Theorem 4, Case 2, (B.9)–(B.10)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem step3_case2_add_product {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St)
    (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (hro : ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i))
    (hsub : S (Fin.last (M + 1)) ⊂ St) (j : Fin n) (hj : j.val = (S (Fin.last (M + 1))).card) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (insert j (S (Fin.last (M + 1))))) := by sorry

end MultiStoreAssort.SQR
