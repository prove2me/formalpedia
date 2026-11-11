-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_B_4
-- name    : GaussPolyReg.Approx.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:28.207297+00:00
-- url     : https://prove2.me/theorems/1d0f5de8-97d9-45e9-9aa8-0fae1bc24017
-- title:
--   Lemma B.4 — joint moment diagram bound (corrected: δ ≥ 0)
-- statement:
--   Let $d_a\ge1$, $p_a\in H_{d_a}(X_1,\ldots,X_n)$, and $\mathbb E p_a^2\le1$. Let $P_a$ be their symmetric coefficient tensors and suppose every proper flattening has spectral norm at most $\delta\ge0$. Let $Z$ be any centered Gaussian vector with covariance $\mathbb E p_ap_b$, and put $D=\sum_a d_a$. If $D$ is even,
--
--   $$\left|\mathbb E\prod_a p_a-\mathbb E\prod_a Z_a\right|\le\frac{(D-1)!!}{\sqrt{\prod_a d_a!}}\,\delta.$$
--
--   If $D$ is odd, both expectations are zero. This estimates the error in replacing chaos vectors by Gaussian vectors with the same covariance.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - correction: δ has no stated sign restriction → 0 ≤ δ; reason: n=1,k=2,d₁=d₂=1,p₁=p₂=X₁,Z=(X₁,X₁),δ=−1 satisfy every printed assumption but give 0 ≤ −1; the nonnegative error parameter is necessary
--   - encoding: symmetric coefficient tensors, spectral norms and a centered Gaussian vector of the same covariance → tensors computed by Hermite coefficient integrals, Euclidean unit-ball operator norms, and Gaussian laws of every linear combination; reason: implements (3.3), the ℓ² spectral norm, and all centered Gaussian laws including singular covariances
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma B.4, p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

/-- Lemma B.4 (corrected: δ ≥ 0). Without this condition, k=2, both degrees
one, p₁=p₂=X₁, δ=-1 gives 0 ≤ -1. The flattening hypotheses are vacuous. -/
theorem lemma_B_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n k : ℕ) (d : Fin k → ℕ) (hd : ∀ a, 1 ≤ d a)
    (p : Fin k → Original) (hp : ∀ a, p a ∈ finiteChaos n (d a))
    (hnorm : ∀ a, ‖p a‖ ^ 2 ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hflat : ∀ a r, 0 < r → r < d a →
      flattenNorm (coefficientTensor (n := n) (d := d a) (p a)) r ≤ δ)
    (Z : Ω → Vec k)
    (hZ : IsCenteredGaussian μ Z (fun a b => pairing (p a) (p b))) :
    (Even (∑ a, d a) →
      |(∫ x, ∏ a, p a x ∂gaussianProduct ℕ) - (∫ x, ∏ a, Z x a ∂μ)| ≤
        (((∑ a, d a)-1).doubleFactorial : ℝ) /
          Real.sqrt (∏ a, (d a).factorial : ℝ) * δ) ∧
    (Odd (∑ a, d a) →
      (∫ x, ∏ a, p a x ∂gaussianProduct ℕ) = 0 ∧ (∫ x, ∏ a, Z x a ∂μ) = 0) := by sorry

end GaussPolyReg.Approx
