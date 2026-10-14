-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_theorem5a_sqr_ge_smr
-- name    : MultiStoreAssort.SMR.theorem5a_sqr_ge_smr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:13.841808+00:00
-- url     : https://prove2.me/theorems/e879636e-2947-40eb-b865-2e72389b2235
-- title:
--   Theorem 5(a), PDF p. 21 — the optimal SQR revenue is at least the optimal SMR revenue
-- statement:
--   In the multi-store model, assume $\lambda_i\ge0$, $\sum_i\lambda_i=1$, $r_1>\dots>r_n>0$, $v_k>0$, $c_{ij}^k\ge0$ and $c_{ii}^k=0$. Let $R_M(\mathbf S)=\sum_i\lambda_i\sum_kr_kp^M_{ik}(\mathbf S)$ be the simultaneous (SMR) revenue and $R_Q(\mathbf S)=\sum_i\lambda_i\sum_kr_kp^Q_{ik}(\mathbf S)$ the sequential (SQR) revenue, with choice probabilities (1) and (2). Then
--   $$\max_{\mathbf S}R_Q(\mathbf S)\ \ge\ \max_{\mathbf S}R_M(\mathbf S).$$
--
--   The paper reads this as: the sequential strategy always leads to higher revenue than the simultaneous one.
--
--   **Formalization Note.** "Higher" is weak: the paper's proof gives $R^*_Q\ge R^*_M$, and equality occurs, for example when $m=1$. The comparison of optimal values is written without a maximum operator: for every profile $\mathbf S$ there is a profile $\mathbf S'$ with $R_M(\mathbf S)\le R_Q(\mathbf S')$. The Gumbel derivation of (2) (Proposition 1, from Gao et al. 2021) is not formalized; (2) is taken as the model. $r_k>0$ is the series' standing assumption.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 21, Theorem 5(a); proof Online Supplement App. C.1, PDF p. 45

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- Theorem 5(a), p. 21: the SQR strategy always leads to (weakly) higher revenue than the SMR
strategy: the optimal (SQR) value is at least the optimal (SMR) value. -/
theorem theorem5a_sqr_ge_smr {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0) :
    ∀ S : Fin m → Finset (Fin n), ∃ S' : Fin m → Finset (Fin n),
      revM lam r v c S ≤ revQ lam r v c S' := by sorry

end MultiStoreAssort.SMR
