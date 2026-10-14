-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_propositionA2_monotone
-- name    : MultiStoreAssort.SMR.propositionA2_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:08.742043+00:00
-- url     : https://prove2.me/theorems/a69fae75-afb3-4c8b-894a-fc1464b5c2ac
-- title:
--   Proposition A.2, PDF p. 33 — larger utility discounts c ≥ c̃ give a larger optimal value, R*_M(c) ≥ R*_M(c̃)
-- statement:
--   Fix revenues $r_1>\dots>r_n>0$, attraction values $v_k>0$ and an assortment $S_2$. Let $R^*_M(\mathbf c)$ be the optimal value of store 1's problem (A.1),
--   $$R^*_M(\mathbf c)=\max_{S_1}\frac{\sum_{k\in S_1}r_kv_k+\sum_{k\in S_2\setminus S_1}r_kv_ke^{-c^k}}{1+\sum_{k\in S_1}v_k+\sum_{k\in S_2\setminus S_1}v_ke^{-c^k}}.$$
--   If $\mathbf c\ge\tilde{\mathbf c}$ componentwise, with $c^k,\tilde c^k\in[0,\infty]$, then
--   $$R^*_M(\mathbf c)\ \ge\ R^*_M(\tilde{\mathbf c}).$$
--
--   Larger discounts make the other store's products less attractive to store 1's customers, so store 1 loses less demand to them. In the proof of Theorem 1 this compares a store's revenue under any profile with the single-store optimum, which is the case $\tilde{\mathbf h}=(\infty,\dots,\infty)$.
--
--   **Formalization Note.** With $\beta_k=e^{-c^k}$ and $\beta'_k=e^{-\tilde c^k}$, the hypothesis $\mathbf c\ge\tilde{\mathbf c}$ reads $0\le\beta_k\le\beta'_k\le1$. The conclusion "$\max$ under $\beta$ $\ge$ $\max$ under $\beta'$" is stated without a maximum operator: for every $T$ there is an $S$ with $R(T;\beta')\le R(S;\beta)$. The paper's definition of $\mathbf c\ge\tilde{\mathbf c}$ also requires $c^i>\tilde c^i$ for at least one $i$. Dropping that clause adds only the case $\mathbf c=\tilde{\mathbf c}$, where the claim is trivial. $\tilde c^k=0$ ($\beta'_k=1$) is allowed, as the model allows $c_{ij}^k=0$. $r_k>0$ is the series' standing assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 33 (Online Supplement p. 1), Proposition A.2; proof Additional Supplement App. A, PDF pp. 49–50

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Proposition A.2, Online Supplement p. 1: if `c ≥ c̃` then `R*_M(c) ≥ R*_M(c̃)`. With
`β = exp(−c)` and `β' = exp(−c̃)`, `c ≥ c̃` is `β ≤ β'` pointwise; the optimal value of (A.1)
under `β` is at least that under `β'`. -/
theorem propositionA2_monotone {n : ℕ} (r v : Fin n → ℝ) (S2 : Finset (Fin n)) (β β' : Fin n → ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hβ0 : ∀ k, 0 ≤ β k) (hββ' : ∀ k, β k ≤ β' k) (hβ'1 : ∀ k, β' k ≤ 1) :
    ∀ T : Finset (Fin n), ∃ S : Finset (Fin n), revA1 r v S2 β' T ≤ revA1 r v S2 β S := by sorry

end MultiStoreAssort.SMR
