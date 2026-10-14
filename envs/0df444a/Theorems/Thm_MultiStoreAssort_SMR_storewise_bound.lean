-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_storewise_bound
-- name    : MultiStoreAssort.SMR.storewise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:07.756907+00:00
-- url     : https://prove2.me/theorems/063a5f07-04f2-4b9c-8781-1aa4e46e6c22
-- title:
--   Proof of Theorem 1, PDF p. 33 — under any profile every store earns at most R* = R*_M(h̃), and exactly R* under (S̃, …, S̃)
-- statement:
--   Assume $r_1>\dots>r_n>0$, $v_k>0$, $c_{ij}^k\ge0$ and $c_{ii}^k=0$. Let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3), and let $R^*=\sum_{k\in\tilde S}r_kv_k/(1+\sum_{k\in\tilde S}v_k)$ be its optimal value. Then:
--   1. for every assortment profile $\mathbf S$ and every store $i$,
--   $$\sum_{k=1}^n r_k\,p^M_{ik}(\mathbf S)\le R^*;$$
--   2. under the profile $(\tilde S,\dots,\tilde S)$ every store $i$ earns exactly $R^*$.
--
--   In the paper, $R^*$ appears as $R^*_M(\tilde{\mathbf h})$ with $\tilde{\mathbf h}=(\infty,\dots,\infty)$: when the other stores' products are discounted away, problem (A.2) is the single-store problem (3). This is the store-wise step of the proof of Theorem 1.
--
--   **Formalization Note.** The paper writes the argument for store 1 and ends with "Repeat this argument for all stores". The Lean statement quantifies over every store $i$. $r_k>0$ is the series' standing assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 33 (Online Supplement p. 1), App. A.1, proof of Theorem 1

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Proof of Theorem 1, Online Supplement p. 1: every store earns at most the single-store optimum
`R* = R*_M(h̃)` under any profile `S`, and exactly `R*` under `(S̃, …, S̃)`. -/
theorem storewise_bound {m n : ℕ} (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Finset (Fin n)) (hSt : IsStilde r v St) :
    (∀ (S : Fin m → Finset (Fin n)) (i : Fin m), storeRevM r v c S i ≤ single r v St) ∧
      ∀ i : Fin m, storeRevM r v c (fun _ => St) i = single r v St := by sorry

end MultiStoreAssort.SMR
