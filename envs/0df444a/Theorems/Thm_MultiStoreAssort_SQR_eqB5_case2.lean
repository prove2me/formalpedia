-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_eqB5_case2
-- name    : MultiStoreAssort.SQR.eqB5_case2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:22.485323+00:00
-- url     : https://prove2.me/theorems/e5c48e20-e344-4112-8dfb-23f28953870f
-- title:
--   (B.5), PDF p. 41 — Case 2 of Prop. B.2: R(𝐒*) ≤ max{R(S*₁,…,S*ₘ₋₁,S*ₘ∪{k}), R(S*₁,…,S*ₘ₋₁,S*ₘ,ₗ)}
-- statement:
--   Consider the SQR problem with $m\ge 2$ stores, store-wise homogeneous discounts $c_{ij}^k=c_i>0$ with $c_1\le\dots\le c_m$, and $\lambda_m=\min_i\lambda_i$. Let $(S_1,\dots,S_m)$ be any nested profile, $S_1\subseteq\dots\subseteq S_m$, let $k$ be the smallest product index with $k\notin S_m$, and write $S_{m,l}=\{j\in S_m: j<k\}$. Suppose we are in Case 2,
--   $$
--   S_{m-1}\subseteq S_{m,l}.
--   $$
--   Then
--   $$
--   R(S_1,\dots,S_m)\le\max\big\{R(S_1,\dots,S_{m-1},S_m\cup\{k\}),\ R(S_1,\dots,S_{m-1},S_{m,l})\big\}.
--   $$
--
--   This is inequality (B.5) of the proof of Proposition B.2, the counterpart of (B.4) when store $m-1$ already lies inside the revenue-ordered head of store $m$.
--
--   **Formalization Note.** As for (B.4), the inequality is stated for every nested profile rather than only for an optimal one; the paper's assumption that $S_m$ is not revenue-ordered is omitted. The standing assumptions of §3 are hypotheses, revenues are positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 41, Appendix B.5, proof of Proposition B.2, Case 2, (B.5)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem eqB5_case2 {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (k : Fin n) (hk : k ∉ S (Fin.last (M + 1))) (hkmin : ∀ j, j < k → j ∈ S (Fin.last (M + 1)))
    (hcase : S (Fin.last M).castSucc ⊆ (S (Fin.last (M + 1))).filter (fun j => j < k)) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      max (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (insert k (S (Fin.last (M + 1))))))
        (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1))
          ((S (Fin.last (M + 1))).filter (fun j => j < k)))) := by sorry

end MultiStoreAssort.SQR
