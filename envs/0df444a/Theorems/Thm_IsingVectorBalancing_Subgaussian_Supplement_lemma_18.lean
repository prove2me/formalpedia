-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_lemma_18
-- name    : IsingVectorBalancing.Subgaussian.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:21:36.677121+00:00
-- url     : https://prove2.me/theorems/64ac5b47-8735-4eff-8bf5-0f67d2728de2
-- title:
--   Lemma 18 — Simultaneous interpolation of every function and all coordinate residuals
-- statement:
--   Assume the Section 8 setting: $n,q\ge2$, $A$ is symmetric, entrywise nonnegative, has at most one positive eigenvalue and no zero row; activities $\lambda_i(a)\ge0$ have $Z_A(\lambda)>0$. For $\delta>0$ let $S=\{0,\pm\delta\}^{nq}$, and put $\Psi_z(\sigma)=\prod_i(1-z_{i,\sigma_i})$. For every real function $f$ on $[q]^n$ there is one family of real coefficients $(b_z)_{z\in S}$ such that, simultaneously for every $\sigma$ with $\mu_{A,\lambda}(\sigma)>0$,
--
--   $$\sum_{z\in S}b_z\Psi_z(\sigma)=f(\sigma),$$
--
--   $$\sum_{z\in S}b_z z_{i,a}\Psi_z(\sigma)=(D_i f)(\sigma)\quad\text{for every site }i\text{ and every color }a.$$
--
--   Here $D_i=I-P_i$ uses the conditional Gibbs average, extended by zero on null fibers. Both identities and the universal color quantifier support Theorem 16. The coefficients are chosen once for $f$ and $\delta$, before all configurations, sites and colors. No $c_A>0$ premise is imposed.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
--   - encoding: the complete grid S={0,±δ}^{nq} → all maps Fin n → Fin q → Fin 3 decoded as 0,δ,−δ; reason: δ>0 makes this a bijection, preserving both sums and the single coefficient family
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 19 (PDF 20), Lemma 18, (27)–(28); proof pp. 19–20 (PDF 20–21)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_TestProducts

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Lemma 18, both (27) and (28), p.19/PDF20. One simultaneous coefficient family. -/
theorem lemma_18 {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (A : Matrix (Fin q) (Fin q) ℝ) (hA : ColorInteraction A)
    (activity : Fin n → Fin q → ℝ) (hactivity : ∀ i a, 0 ≤ activity i a)
    (hZ : 0 < colorPartition A activity) (δ : ℝ) (hδ : 0 < δ)
    (f : ColorConfiguration n q → ℝ) :
    ∃ b : GridIndex n q → ℝ, ∀ σ : ColorConfiguration n q, 0 < colorLaw A activity σ →
      (∑ z : GridIndex n q, b z * psi (gridPoint δ z) σ) = f σ ∧
      ∀ (i : Fin n) (a : Fin q),
        (∑ z : GridIndex n q, b z * gridPoint δ z i a * psi (gridPoint δ z) σ) =
          SpinGirth5.singleLap (colorLaw A activity) i f σ := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
