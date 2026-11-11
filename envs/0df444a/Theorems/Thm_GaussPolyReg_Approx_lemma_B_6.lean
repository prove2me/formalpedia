-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_B_6
-- name    : GaussPolyReg.Approx.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:44.427209+00:00
-- url     : https://prove2.me/theorems/978dae1b-c3b7-4cc0-8880-f9ed7bb68a50
-- title:
--   Lemma B.6 — norm of a top product (corrected: δ ≥ 0)
-- statement:
--   Let $d_a\ge1$, $D=\sum_a d_a$, and $p_a\in H_{d_a}(X_1,\ldots,X_n)$ with $\mathbb E p_a^2=1$. Suppose every proper coefficient-tensor flattening has spectral norm at most $\delta\ge0$. Let $\mathcal M(2,k)$ be all bijections between two copies of $[k]$. Then
--
--   $$\left|\mathbb E\left(\mathop{\diamond}_{a=1}^k p_a\right)^2-\sum_{M\in\mathcal M(2,k)}\prod_{uv\in M}\mathbb E[p_up_v]\right|\le\frac{D!}{\prod_a d_a!}\,\delta.$$
--
--   The denominator has no square root. This supplies the top-product norm estimate used to identify the limiting Hermite basis.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - correction: δ has no stated sign restriction → 0 ≤ δ; reason: n=k=d₁=1,p₁=X₁,δ=−1 satisfy every printed assumption but give 0 ≤ −1; the nonnegative error parameter is necessary
--   - encoding: iterated top product and perfect matchings between two copies → one projection of the ordinary product to degree D, and the covariance permanent over permutations; reason: associativity of the top product identifies the projection with its iteration; permutations are precisely those two-copy matchings
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma B.6, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

/-- Lemma B.6 (corrected: δ ≥ 0). Without it, k=1, d₁=1, p₁=X₁,
δ=-1 satisfies the vacuous flattening hypothesis but the bound is 0 ≤ -1. -/
theorem lemma_B_6 (n k : ℕ) (d : Fin k → ℕ) (hd : ∀ a, 1 ≤ d a)
    (p : Fin k → Original) (hp : ∀ a, p a ∈ finiteChaos n (d a))
    (hnorm : ∀ a, ‖p a‖ ^ 2 = 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hflat : ∀ a r, 0 < r → r < d a →
      flattenNorm (coefficientTensor (n := n) (d := d a) (p a)) r ≤ δ) :
    |‖iteratedTop d p‖ ^ 2 - covariancePermanent p| ≤
      ((∑ a, d a).factorial : ℝ) / (∏ a, (d a).factorial : ℝ) * δ := by sorry

end GaussPolyReg.Approx
