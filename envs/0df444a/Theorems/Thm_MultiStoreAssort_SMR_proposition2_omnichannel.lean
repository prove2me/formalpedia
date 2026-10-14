-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_proposition2_omnichannel
-- name    : MultiStoreAssort.SMR.proposition2_omnichannel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:09.919031+00:00
-- url     : https://prove2.me/theorems/71de23e1-893d-4865-b13a-e394fa0f0cd8
-- title:
--   Proposition 2, PDF p. 13 — omnichannel S_m = 𝒩 with c_{im}^k = c^k > 0: identical revenue-ordered physical-store optima, larger than S̃
-- statement:
--   Consider the multi-store SMR model with stores $1,\dots,m$, where store $m$ is an online channel that offers every product, $S_m=\mathcal N=\{1,\dots,n\}$. Assume $\lambda_i\ge0$, $\sum_i\lambda_i=1$, $r_1>\dots>r_n>0$, $v_k>0$, $c_{ij}^k\ge0$, $c_{ii}^k=0$, and that buying online costs every physical-store customer the same discount, $c_{im}^k=c^k>0$ for $i\in\{1,\dots,m-1\}$ and every product $k$. Let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3). Then there is a revenue-ordered assortment $\hat S\supseteq\tilde S$ such that the profile $(\hat S,\dots,\hat S,\mathcal N)$ is optimal for (SMR) among all profiles with $S_m=\mathcal N$:
--   $$\sum_{i=1}^m\lambda_i\sum_{k=1}^nr_kp^M_{ik}(\mathbf S)\ \le\ \sum_{i=1}^m\lambda_i\sum_{k=1}^nr_kp^M_{ik}(\hat S,\dots,\hat S,\mathcal N)\qquad\text{whenever }S_m=\mathcal N.$$
--   So the optimal assortments of the $m-1$ physical stores can be taken identical and revenue-ordered, and larger than $\tilde S$.
--
--   The online channel cannibalizes the physical stores, which lowers each store's revenue threshold, so more products clear it.
--
--   **Formalization Note.** Stores are `Fin (M+1)`, and store $m$ is `Fin.last M`. The discounts between physical stores stay arbitrary, as on the page. "Optimal assortments … are identical and revenue-ordered" is read as the existence of an optimal profile of that form, since ties are possible. "Larger than $\tilde S$" is read as $\tilde S\subseteq\hat S$; for two revenue-ordered sets this is the same as $|\tilde S|\le|\hat S|$, which is where the paper's proof ends. When $m=1$ the statement is trivially true. $r_k>0$ is the series' standing assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 13, Proposition 2; proof Online Supplement App. A.4, PDF p. 34

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Proposition 2, p. 13: in the omnichannel setting (store `m` = `Fin.last M` offers every
product) with `c_{im}^k = c^k > 0` for the physical stores `i`, some optimal SMR profile with
`S_m = 𝒩` offers one and the same revenue-ordered assortment `Ŝ ⊇ S̃` in every physical store. -/
theorem proposition2_omnichannel {M n : ℕ} (lam : Fin (M + 1) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 1) → Fin (M + 1) → Fin n → ℝ) (cbar : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (hcm : ∀ i k, i ≠ Fin.last M → c i (Fin.last M) k = cbar k) (hcbar : ∀ k, 0 < cbar k)
    (St : Finset (Fin n)) (hSt : IsStilde r v St) :
    ∃ Shat : Finset (Fin n), IsRevenueOrdered Shat ∧ St ⊆ Shat ∧
      ∀ S : Fin (M + 1) → Finset (Fin n), S (Fin.last M) = Finset.univ →
        revM lam r v c S ≤
          revM lam r v c (fun i => if i = Fin.last M then Finset.univ else Shat) := by sorry

end MultiStoreAssort.SMR
