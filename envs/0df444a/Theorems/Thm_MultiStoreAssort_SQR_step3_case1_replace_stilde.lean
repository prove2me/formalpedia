-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_step3_case1_replace_stilde
-- name    : MultiStoreAssort.SQR.step3_case1_replace_stilde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:23.640544+00:00
-- url     : https://prove2.me/theorems/bf2ef4c1-1469-46c6-bff8-6053c9fef6d3
-- title:
--   Proof of Theorem 4, Step 3, Case 1, (B.6)–(B.8), PDF pp. 42–43 — replacing S*ₖ₊₁,…,S*ₘ₋₁ by S̃ does not decrease the revenue
-- statement:
--   Consider the SQR problem with $m\ge2$ stores, store-wise homogeneous discounts $c_{ij}^k=c_i>0$ with $c_1\le\dots\le c_m$, and $\lambda_m=\min_i\lambda_i$. Let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3). Let $(S_1,\dots,S_m)$ be a profile of revenue-ordered assortments with $S_1\subseteq\dots\subseteq S_m$, and suppose we are in Case 1: for some $k\in\{0,\dots,m-2\}$,
--   $$
--   S_1\subseteq\dots\subseteq S_k\subseteq\tilde S\subset S_{k+1}\subseteq\dots\subseteq S_m .
--   $$
--   Then
--   $$
--   R(S_1,\dots,S_k,\tilde S,\dots,\tilde S,S_m)\ \ge\ R(S_1,\dots,S_m),
--   $$
--   where stores $k+1,\dots,m-1$ now offer $\tilde S$.
--
--   This is the conclusion drawn from (B.6), (B.7) and (B.8) in Step 3 of the proof of Theorem 4.
--
--   **Formalization Note.** The paper argues for the optimal solution of Proposition B.2; the inequality is stated for every revenue-ordered nested profile in Case 1. In Lean, $k$ is `K ≤ M` (with $m=M+2$), stores with 0-based index below $K$ satisfy $S_i\subseteq\tilde S$ and the others satisfy $\tilde S\subsetneq S_i$. The standing assumptions of §3 are hypotheses, revenues are positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 42–43, Appendix B.6, proof of Theorem 4, Case 1, (B.6)–(B.8)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem step3_case1_replace_stilde {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St)
    (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (hro : ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i))
    (K : ℕ) (hK : K ≤ M) (hlow : ∀ i : Fin (M + 2), i.val < K → S i ⊆ St)
    (hhigh : ∀ i : Fin (M + 2), K ≤ i.val → St ⊂ S i) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      MultiStoreAssort.SMR.revQ lam r v c (fun i => if K ≤ i.val ∧ i ≠ Fin.last (M + 1) then St else S i) := by sorry

end MultiStoreAssort.SQR
