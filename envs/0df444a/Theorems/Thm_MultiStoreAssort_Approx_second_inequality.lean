-- Prove2me | Theorems.Thm_MultiStoreAssort_Approx_second_inequality
-- name    : MultiStoreAssort.Approx.second_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:50.520876+00:00
-- url     : https://prove2.me/theorems/43b18c39-50e1-4d75-af09-83b82fdbcc76
-- title:
--   Proof of Proposition 7, PDF p. 47 — every profile earns at most twice the sum of single-store optima
-- statement:
--   In the heterogeneous multi-store model ($m$ stores with arrival fractions $\lambda_i\ge0$, $\sum_i\lambda_i=1$; $n$ products with revenues $r_1>r_2>\dots>r_n>0$; attraction values $v_{ik}>0$; utility discounts $c^k_{ij}\ge0$ with $c^k_{ii}=0$), let $R(\boldsymbol S)$ be the (SQR-heter) revenue of a profile $\boldsymbol S$. For each store $i$ let $\tilde S_i$ be an optimal solution of store $i$'s single-store problem
--   $$
--   R^*_i=\max_S\frac{\sum_{k\in S}r_kv_{ik}}{1+\sum_{k\in S}v_{ik}}.\qquad\text{(D.1)}
--   $$
--   Then for every profile $\boldsymbol S=(S_1,\dots,S_m)$,
--   $$
--   R(\boldsymbol S)\ \le\ 2\sum_{i=1}^m\lambda_i\cdot\frac{\sum_{k\in\tilde S_i}r_kv_{ik}}{1+\sum_{k\in\tilde S_i}v_{ik}}=2\sum_{i=1}^m\lambda_iR^*_i.
--   $$
--
--   Each store's revenue under $\boldsymbol S$ splits into a first stage (the store's own assortment) and a second stage (the other stores' products, with discounted attraction values); each part is at most $R^*_i$. Applied to an optimal profile $\boldsymbol S^*$ of (SQR-heter) this is the second and third inequality of the proof of Proposition 7, $\sum_i\lambda_iR^*_i\ge\frac12R^*_Q$.
--
--   **Formalization Note.** The statement only uses that each $\tilde S_i$ is *an* optimal solution of (D.1), not the paper's tie rule, and it is stated for every profile $\boldsymbol S$ instead of an optimal one; both are generalizations covered by the paper's argument. The positivity of the revenues is pinned, as in the rest of the mission.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 47 (Online Supplement p. 15), Appendix D.2, proof of Proposition 7, second and third inequalities; (D.1) on PDF p. 46

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

namespace MultiStoreAssort.Approx

/-- Second and third inequalities of the proof of Proposition 7 (Online Supplement p. 15): if each
`St i` is an optimal solution of store `i`'s single-store problem (D.1), then every profile `S`
earns at most twice `∑_i λ_i ∑_{k ∈ S̃_i} r_k v_{ik} / (1 + ∑_{k ∈ S̃_i} v_{ik})` under (SQR-heter). -/
theorem second_inequality {m n : ℕ} (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ i k, 0 < v i k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Fin m → Finset (Fin n)) (hSt : ∀ i, MultiStoreAssort.SMR.IsOptSingle r (v i) (St i)) :
    ∀ S : Fin m → Finset (Fin n),
      revQh lam r v c S ≤ 2 * ∑ i, lam i * MultiStoreAssort.SMR.single r (v i) (St i) := by sorry

end MultiStoreAssort.Approx
