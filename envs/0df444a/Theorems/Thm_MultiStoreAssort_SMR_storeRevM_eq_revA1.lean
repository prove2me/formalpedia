-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_storeRevM_eq_revA1
-- name    : MultiStoreAssort.SMR.storeRevM_eq_revA1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:06.480612+00:00
-- url     : https://prove2.me/theorems/ca002c28-f2c0-4a24-8e5f-a8cc16b72d63
-- title:
--   Proof of Theorem 1, PDF p. 33 — store i's SMR revenue under S is R(S_i, h) of (A.2)
-- statement:
--   Let $\mathbf S=(S_1,\dots,S_m)$ be any assortment profile and $i$ a store. Let $S_{\hat2}=\bigcup_{j\ne i}S_j$ be the union of the other stores' assortments, and let $e^{-h^k}=e^{-c_i^k(\mathbf S)}$ be the discount factor of product $k$ for a customer of store $i$. Then store $i$'s expected revenue under the simultaneous recommendation model equals the two-store objective (A.2):
--   $$\sum_{k=1}^n r_k\,p^M_{ik}(\mathbf S)=R(S_i,\mathbf h)=\frac{\sum_{k\in S_i}r_kv_k+\sum_{k\in S_{\hat2}\setminus S_i}r_kv_ke^{-h^k}}{1+\sum_{k\in S_i}v_k+\sum_{k\in S_{\hat2}\setminus S_i}v_ke^{-h^k}}.$$
--
--   The identity rewrites the SMR revenue of one store as the objective of a single-store problem in which the other stores act as a source of discounted outside products. This rewriting is what lets the proof of Theorem 1 argue store by store.
--
--   **Formalization Note.** The paper writes the argument for store 1 with $h^k=\min_{j\in\{l\mid k\in S_l,\ l=2,\dots,m\}}c_{1j}^k$. The Lean statement is for every store $i$, and uses `discFactor c S i`, the factor $e^{-c_i^k(\mathbf S)}$ over all offering stores. It agrees with $e^{-h^k}$ for every $k\notin S_i$, the only products where it is used. The proof as printed has $S^*_l$ where $S_l$ is meant. The identity needs no hypotheses.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 33 (Online Supplement p. 1), App. A.1, proof of Theorem 1, (A.2) and the sentence 'We notice that R(S₁, h) is the expected revenue of store 1 under the solution S'

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Proof of Theorem 1, Online Supplement p. 1: store `i`'s SMR revenue under `S` is
`R(S_i, h)` of (A.2), where the other stores offer `S_2̂ = ⋃_{j ≠ i} S_j` and
`exp(−h^k) = exp(−c_i^k(S))`. -/
theorem storeRevM_eq_revA1 {m n : ℕ} (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) :
    storeRevM r v c S i =
      revA1 r v ((Finset.univ.filter (fun j => j ≠ i)).sup S) (discFactor c S i) (S i) := by sorry

end MultiStoreAssort.SMR
