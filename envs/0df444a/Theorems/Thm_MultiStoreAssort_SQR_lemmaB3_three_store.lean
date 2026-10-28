-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_lemmaB3_three_store
-- name    : MultiStoreAssort.SQR.lemmaB3_three_store
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:04.96183+00:00
-- url     : https://prove2.me/theorems/183ba0ae-88b3-434b-990d-a6a2e79a2748
-- title:
--   Lemma B.3, PDF p. 36 — in a 3-store, 4-product SQR instance, R({{1,2},{1,3},{4}}) ≤ max(R({{1},{1,2,3},{4}}), R({{1,2},{1,2,3},{4}}))
-- statement:
--   Consider the SQR problem with three stores and four products, with revenues $R_1,R_2,R_3,R_4\ge 0$ and attraction values $V_1,V_2,V_3,V_4\ge 0$. Let $\lambda_1=\lambda_2=\tfrac12$ and $\lambda_3=0$, and let the utility discounts be store-wise homogeneous: $c_{ij}^k=c_i>0$ for $i\ne j$ (and $c_{ii}^k=0$). Assume $R_2\ge R_3$ and $c_1\le c_2$. Consider the three recommendation strategies
--   $$
--   \mathbf S=(\{1,2\},\{1,3\},\{4\}),\quad \mathbf S_1=(\{1\},\{1,2,3\},\{4\}),\quad \mathbf S_2=(\{1,2\},\{1,2,3\},\{4\}).
--   $$
--   Then the SQR revenues satisfy
--   $$
--   R(\mathbf S)\le \max\big(R(\mathbf S_1),R(\mathbf S_2)\big).
--   $$
--
--   In the proof of Proposition B.1 the four products stand for the proxy products $S_1^*\cap S_m^*$, $S_1^*\setminus S_m^*$, $S_m^*\setminus S_1^*$ and $\bar S\setminus(S_1^*\cup S_m^*)$, and the lemma shows that moving the products of store 1 into store $m$ never hurts.
--
--   **Formalization Note.** $R(\cdot)$ is the general SQR objective `revQ` evaluated on this instance (products $1,\dots,4$ are indices $0,\dots,3$). The revenues are not assumed ordered, since they are proxy revenues. Nonnegative revenues are a pinned hypothesis: the statement fails for $R=(1,0,0,-8)$, $V\equiv 1$, $e^{-c_1}=\tfrac12$, $e^{-c_2}=\tfrac14$. Attraction values may be $0$ (an empty proxy product), which generalizes the paper's positive attraction values.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 36, Lemma B.3 (proof in the Additional Supplement, PDF pp. 50–53)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem lemmaB3_three_store (R V : Fin 4 → ℝ) (c : Fin 3 → Fin 3 → Fin 4 → ℝ) (c₁ c₂ c₃ : ℝ)
    (hR : ∀ k, 0 ≤ R k) (hV : ∀ k, 0 ≤ V k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c ![c₁, c₂, c₃]) (hR23 : R 2 ≤ R 1) (hc12 : c₁ ≤ c₂) :
    MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0, 1}, {0, 2}, {3}] : Fin 3 → Finset (Fin 4)) ≤
      max (MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0}, {0, 1, 2}, {3}] : Fin 3 → Finset (Fin 4)))
        (MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0, 1}, {0, 1, 2}, {3}] : Fin 3 → Finset (Fin 4))) := by sorry

end MultiStoreAssort.SQR
