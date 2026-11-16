-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_lemma_17
-- name    : IsingVectorBalancing.Subgaussian.Supplement.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:20:37.440569+00:00
-- url     : https://prove2.me/theorems/4ed3e38e-3439-463f-bcf9-624473cf8df7
-- title:
--   Lemma 17 — Variance inequality for arbitrary finite signed combinations of spin-system test products
-- statement:
--   Assume the Section 8 setting: $n,q\ge2$, $A$ is symmetric, entrywise nonnegative, has at most one positive eigenvalue and no zero row; activities $\lambda_i(a)\ge0$ have $Z_A(\lambda)>0$. Fix a positive-vector decomposition $A_{ab}=\rho_a\rho_b-\langle R_a,R_b\rangle$ and put $v_a=R_a/\rho_a$. In any finite Euclidean dimension, let $w_i^a$ have norm at most one and satisfy
--
--   $$\langle w_j^a,w_k^b\rangle=\langle v_a,v_b\rangle\quad(j\ne k,\ a,b\in[q]).$$
--
--   For any finite set $U$ of unit-ball vectors and arbitrary real coefficients $c_u$, set $\Phi_u^w(\sigma)=\prod_i(1-\langle u,w_i^{\sigma_i}\rangle)$. Then
--
--   $$\operatorname{Var}_{\mu_{A,\lambda}}\left(\sum_{u\in U}c_u\Phi_u^w\right)\le\mathbb E_{\mu_{A,\lambda}}\left\|\sum_{u\in U}c_u u\Phi_u^w\right\|_2^2.$$
--
--   This supports Theorem 16. Empty $U$, signed coefficients and arbitrary same-site Gram matrices are retained; no $c_A>0$ premise is imposed.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
--   - generalization: the Perron–Frobenius decomposition (23) → every positive-vector decomposition satisfying (23); reason: the proof uses only that identity and positivity of ρ, and therefore includes the source choice
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 18 (PDF 19), Lemma 17, (25); setup p. 17 (PDF 18), (21)–(24)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_TestProducts

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Lemma 17, (25), p.18/PDF19. Coefficients are arbitrary signed reals. -/
theorem lemma_17 {n q r d : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (A : Matrix (Fin q) (Fin q) ℝ) (hA : ColorInteraction A)
    (activity : Fin n → Fin q → ℝ) (hactivity : ∀ i a, 0 ≤ activity i a)
    (hZ : 0 < colorPartition A activity) (D : PositiveDecomposition A r)
    (w : Fin n → Fin q → Vec d) (hw : ∀ i a, ‖w i a‖ ≤ 1)
    (hGram : ∀ j k, j ≠ k → ∀ a b,
      inner ℝ (w j a) (w k b) = inner ℝ (normalizedRow D a) (normalizedRow D b))
    (U : Finset (Vec d)) (c : Vec d → ℝ) (hU : ∀ u ∈ U, ‖u‖ ≤ 1) :
    SubsetConvFPRAS.variance (colorLaw A activity) (fun σ => ∑ u ∈ U, c u * phi w u σ) ≤
      SubsetConvFPRAS.expect (colorLaw A activity)
        (fun σ => ‖∑ u ∈ U, (c u * phi w u σ) • u‖ ^ 2) := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
