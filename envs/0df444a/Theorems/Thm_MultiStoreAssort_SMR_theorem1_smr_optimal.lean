-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_theorem1_smr_optimal
-- name    : MultiStoreAssort.SMR.theorem1_smr_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:15.831759+00:00
-- url     : https://prove2.me/theorems/5f048cb6-ac7f-4c24-aa62-e9eb97932ce7
-- title:
--   Theorem 1, PDF p. 11 — under simultaneous recommendation the profile (S̃, …, S̃) is optimal
-- statement:
--   A seller operates $m$ stores and sells $n$ products with revenues $r_1>r_2>\dots>r_n>0$ and MNL attraction values $v_k>0$. A fraction $\lambda_i\ge0$ of customers visits store $i$, with $\sum_i\lambda_i=1$. A customer who visits store $i$ and buys product $k$ from store $j$ suffers a utility discount $c_{ij}^k\ge0$, with $c_{ii}^k=0$. Under the **simultaneous recommendation (SMR)** model, the customer of store $i$ facing the profile $\mathbf S=(S_1,\dots,S_m)$ chooses product $k$ with probability $p^M_{ik}(\mathbf S)$ given by (1). The seller's problem is
--   $$\max_{\mathbf S=(S_1,\dots,S_m)}\ \sum_{i=1}^m\lambda_i\sum_{k=1}^n r_k\,p^M_{ik}(\mathbf S).\tag{SMR}$$
--   Let $\tilde S$ be the smallest revenue-ordered optimal solution of the single-store problem (3). Then $(\tilde S,\tilde S,\dots,\tilde S)$ is an optimal solution of (SMR): for every profile $\mathbf S$,
--   $$\sum_{i=1}^m\lambda_i\sum_{k=1}^n r_k\,p^M_{ik}(\mathbf S)\ \le\ \sum_{i=1}^m\lambda_i\sum_{k=1}^n r_k\,p^M_{ik}(\tilde S,\dots,\tilde S).$$
--
--   Under simultaneous recommendation, cross-store coordination never beats running every store as a stand-alone MNL store. The resulting revenue is the paper's benchmark, which the sequential strategy is compared against.
--
--   **Formalization Note.** "The optimal solution is $(\tilde S,\dots,\tilde S)$" is formalized as "$(\tilde S,\dots,\tilde S)$ is a global maximizer". Optimal solutions need not be unique. $\tilde S$ enters through the predicate `IsStilde`, and the milestone `stilde_exists` shows such an $\tilde S$ exists. The positivity $r_k>0$ is the series' standing assumption (revenues are prices). Zero discounts $c_{ij}^k=0$ between different stores are allowed, as in the paper.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 11, Theorem 1; proof Online Supplement App. A.1, PDF p. 33

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Theorem 1, p. 11: the optimal solution to the SMR problem is `S* = (S̃, S̃, …, S̃)`. -/
theorem theorem1_smr_optimal {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Finset (Fin n)) (hSt : IsStilde r v St) :
    ∀ S : Fin m → Finset (Fin n), revM lam r v c S ≤ revM lam r v c (fun _ => St) := by sorry

end MultiStoreAssort.SMR
