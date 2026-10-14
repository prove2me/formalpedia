-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_propositionA1_threshold
-- name    : MultiStoreAssort.SMR.propositionA1_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:06.877821+00:00
-- url     : https://prove2.me/theorems/620fe08c-888d-43bd-8093-4ac2ac785926
-- title:
--   Proposition A.1, PDF p. 33 — (A.1) has a revenue-ordered optimum, and r_i > R*_M(c) iff i ∈ S*_M(c)
-- statement:
--   Fix revenues $r_1>\dots>r_n>0$, attraction values $v_k>0$, $n\ge1$, an assortment $S_2$ offered by store 2, and discount factors $\beta_k=e^{-c^k}$ with $0\le\beta_k\le1$, that is $c^k\in[0,\infty]$. Store 1's problem is
--   $$\max_{S_1}\ R(S_1,\mathbf c)=\frac{\sum_{k\in S_1}r_kv_k+\sum_{k\in S_2\setminus S_1}r_kv_k\beta_k}{1+\sum_{k\in S_1}v_k+\sum_{k\in S_2\setminus S_1}v_k\beta_k}.\tag{A.1}$$
--   Write $R^*_M(\mathbf c)$ for its optimal value and $S^*_M(\mathbf c)$ for its smallest revenue-ordered optimal solution. Then:
--   1. some revenue-ordered assortment $\{1,\dots,k\}$ with $k\in[n]$ is optimal for (A.1);
--   2. if moreover $\beta_k<1$ (that is $c^k>0$) for every $k$, then for $S=S^*_M(\mathbf c)$ and every product $i$,
--   $$r_i>R^*_M(\mathbf c)\iff i\in S^*_M(\mathbf c).$$
--
--   The proposition reduces store 1's best response to a revenue threshold. The proof of Theorem 1 uses it through Proposition A.2.
--
--   **Formalization Note.** The paper states the proposition for any $\mathbf c$. Part 1 is stated for every $\mathbf c\ge0$. Part 2 assumes $c^k>0$ ($\beta_k<1$), because the "if and only if" fails when some $c^k=0$. With $n=2$, $r=(3,2)$, $v=(1,1)$, $S_2=\{2\}$ and $c^2=0$, one gets $R^*_M=5/3$ and $S^*_M=\{1\}$, yet $r_2=2>5/3$. The optimal value is read off $S^*_M(\mathbf c)$ as `revA1 r v S₂ β S`. $r_k>0$ is the series' standing assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 33 (Online Supplement p. 1), Proposition A.1; proof Additional Supplement App. A, PDF p. 49

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Proposition A.1, Online Supplement p. 1, for discount factors `β_k = exp(−c^k) ∈ [0, 1]`
(i.e. `c^k ∈ [0, ∞]`): (i) some revenue-ordered assortment is optimal for (A.1); (ii) if moreover
`β_k < 1` for every `k` (i.e. `c^k > 0`), then for `S*_M(c)`, `r_i > R*_M(c)` iff `i ∈ S*_M(c)`.
Part (ii) is false at `c^k = 0` (`n = 2`, `r = (3, 2)`, `v = (1, 1)`, `S_2 = {2}`, `β_2 = 1`). -/
theorem propositionA1_threshold {n : ℕ} (r v : Fin n → ℝ) (S2 : Finset (Fin n)) (β : Fin n → ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hβ0 : ∀ k, 0 ≤ β k) (hβ1 : ∀ k, β k ≤ 1) (hn : 0 < n) :
    (∃ S : Finset (Fin n), IsRevenueOrdered S ∧ ∀ T, revA1 r v S2 β T ≤ revA1 r v S2 β S) ∧
      ((∀ k, β k < 1) → ∀ S : Finset (Fin n), IsSstarM r v S2 β S →
        ∀ i : Fin n, revA1 r v S2 β S < r i ↔ i ∈ S) := by sorry

end MultiStoreAssort.SMR
