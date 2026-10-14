-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_eqB4_case1
-- name    : MultiStoreAssort.SQR.eqB4_case1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:19.377646+00:00
-- url     : https://prove2.me/theorems/1eaeadf1-6580-4429-ba9c-4b5820570bd8
-- title:
--   (B.4), PDF p. 40 — Case 1 of Prop. B.2: R(𝐒*) ≤ max{R(S*₁,…,S*ₘ₋₁,S*ₘ∪{k}), R(S*₁,…,S*ₘ₋₁,S*ₘ₋₁)}
-- statement:
--   Consider the SQR problem with $m\ge 2$ stores, store-wise homogeneous discounts $c_{ij}^k=c_i>0$ with $c_1\le\dots\le c_m$, and $\lambda_m=\min_i\lambda_i$. Let $(S_1,\dots,S_m)$ be any nested profile, $S_1\subseteq S_2\subseteq\dots\subseteq S_m$. Let $k$ be the smallest product index with $k\notin S_m$, and write $S_{m,l}=\{j\in S_m: j<k\}$. Suppose we are in Case 1,
--   $$
--   S_{m,l}\subseteq S_{m-1}.
--   $$
--   Then
--   $$
--   R(S_1,\dots,S_m)\le\max\big\{R(S_1,\dots,S_{m-1},S_m\cup\{k\}),\ R(S_1,\dots,S_{m-1},S_{m-1})\big\}.
--   $$
--
--   This is inequality (B.4) of the proof of Proposition B.2: if the largest assortment is not revenue-ordered, adding the first missing product or cutting it down to $S_{m-1}$ does not lose revenue.
--
--   **Formalization Note.** The paper states (B.4) for an optimal solution, where it would be trivial; it is stated here for every nested profile, which is what the proof establishes. "$k$ is the smallest index not in $S_m$" is the pair of hypotheses $k\notin S_m$ and $j\in S_m$ for every $j<k$; the paper's additional assumption that $S_m$ is not revenue-ordered is not needed and is omitted. The standing assumptions of §3 are hypotheses, revenues are positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 39–40, Appendix B.5, proof of Proposition B.2, Case 1, (B.4)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem eqB4_case1 {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (k : Fin n) (hk : k ∉ S (Fin.last (M + 1))) (hkmin : ∀ j, j < k → j ∈ S (Fin.last (M + 1)))
    (hcase : (S (Fin.last (M + 1))).filter (fun j => j < k) ⊆ S (Fin.last M).castSucc) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      max (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (insert k (S (Fin.last (M + 1))))))
        (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (S (Fin.last M).castSucc))) := by sorry

end MultiStoreAssort.SQR
