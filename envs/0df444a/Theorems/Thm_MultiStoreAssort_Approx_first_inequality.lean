-- Prove2me | Theorems.Thm_MultiStoreAssort_Approx_first_inequality
-- name    : MultiStoreAssort.Approx.first_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:52.276972+00:00
-- url     : https://prove2.me/theorems/83ff7fdb-fc46-405b-b686-06b7c6f3402e
-- title:
--   Proof of Proposition 7, PDF p. 47 — the SQR-heter revenue is at least the first-stage revenue
-- statement:
--   In the heterogeneous multi-store model ($m$ stores with arrival fractions $\lambda_i\ge0$, $\sum_i\lambda_i=1$; $n$ products with revenues $r_1>r_2>\dots>r_n>0$; attraction values $v_{ik}>0$ of product $k$ in store $i$; utility discounts $c^k_{ij}\ge0$ with $c^k_{ii}=0$), let $R(\boldsymbol T)=\sum_{i=1}^m\lambda_i\sum_{k=1}^nr_kp^Q_{ik}(\boldsymbol T)$ be the (SQR-heter) revenue of a profile $\boldsymbol T=(T_1,\dots,T_m)$, with $p^Q_{ik}$ the sequential choice probabilities (10). Then for every profile $\boldsymbol T$,
--   $$
--   R(\boldsymbol T)\ \ge\ \sum_{i=1}^m\lambda_i\cdot\frac{\sum_{k\in T_i}r_kv_{ik}}{1+\sum_{k\in T_i}v_{ik}}.
--   $$
--
--   The right-hand side is the revenue of the first stage, in which each customer considers only the assortment of the store she visits. In the proof of Proposition 7 this is applied to the heuristic profile $(\tilde S_1,\dots,\tilde S_m)$, where it reads $R^H_Q\ge\sum_i\lambda_iR^*_i$.
--
--   **Formalization Note.** The paper writes the inequality for $\boldsymbol T=(\tilde S_1,\dots,\tilde S_m)$; it is stated here for every profile, a generalization the paper's argument covers unchanged. The positivity of the revenues $r_k$ is a pinned hypothesis: the inequality drops the second-stage revenue, which is nonnegative because revenues are prices; the paper never states the sign.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 47 (Online Supplement p. 15), Appendix D.2, proof of Proposition 7, first inequality

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

namespace MultiStoreAssort.Approx

/-- First inequality of the proof of Proposition 7 (Online Supplement p. 15), stated for every
profile `T`: the (SQR-heter) revenue of `T` is at least the revenue of its first stage,
`∑_i λ_i ∑_{k ∈ T_i} r_k v_{ik} / (1 + ∑_{k ∈ T_i} v_{ik})`. -/
theorem first_inequality {m n : ℕ} (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ i k, 0 < v i k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0) :
    ∀ T : Fin m → Finset (Fin n),
      ∑ i, lam i * MultiStoreAssort.SMR.single r (v i) (T i) ≤ revQh lam r v c T := by sorry

end MultiStoreAssort.Approx
