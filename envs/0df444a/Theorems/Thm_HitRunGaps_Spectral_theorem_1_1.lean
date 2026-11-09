-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_theorem_1_1
-- name    : HitRunGaps.Spectral.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:46.519678+00:00
-- url     : https://prove2.me/theorems/9779ca28-5b89-4a24-b998-5b4818ec64ee
-- title:
--   Theorem 1.1 — Spectral gaps
-- statement:
--   There is a universal $c>0$ such that, for every $n\ge2$, bounded open convex $K\subset\mathbb R^n$ containing a unit ball at any center, and any fixed orthonormal coordinate basis, the uniform law $\pi$ has positive finite $C_{PI}(\pi)$ and centered covariance norm, and
--
--   $$\lambda_{HR}\ge\frac{c}{n^2C_{PI}(\pi)},\qquad
--   \frac1{n^2C_{PI}(\pi)}\ge\frac{c}{n^2\|\operatorname{cov}\pi\|_{op}},$$
--   $$\lambda_{CHAR}\ge\frac{c}{n^3C_{PI}(\pi)},\qquad
--   \frac1{n^3C_{PI}(\pi)}\ge\frac{c}{n^3\|\operatorname{cov}\pi\|_{op}}.$$
--
--   The one constant precedes dimension, body, inball center and basis. Neither isotropy nor KLS is an extra hypothesis. The spectral gaps belong to the actual continuous chord samplers. Both Poincaré and covariance comparisons form this single goal.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: finite nonzero constants implicitly used in the displayed real reciprocals → positivity and finiteness of the domain Poincaré constant and centered covariance norm are also conclusions; reason: This prevents an extended-value reciprocal from concealing undefined source data; these facts follow from the stated full-dimensional bounded convex setting
--   - encoding: the operator Dirichlet form of the actual reversible chord sampler → the one-half squared-jump integral against the published chord laws; reason: Reversibility identifies this nonnegative form with the source inner product, so the Rayleigh infimum covers the same L² classes
--   - reading: a unit ball inside K → some open Euclidean ball Metric.ball c 1 ⊆ K, centre arbitrary; reason: the source does not say open or closed; a closed unit ball inside K contains the open one, so the Lean hypothesis is the weaker (more general) reading
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.4, Theorem 1.1

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem theorem_1_1 : ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 2 ≤ n →
    ∀ K : Set (Space n), UnitBody K →
    ∀ b : OrthonormalBasis (Fin n) ℝ (Space n),
      (0 < poincare K ∧ poincare K < ⊤ ∧ 0 < covarianceNorm K ∧ covarianceNorm K < ⊤) ∧
      ENNReal.ofReal c / ((n : ENNReal) ^ 2 * poincare K) ≤ hitRunGap K ∧
      ENNReal.ofReal c / ((n : ENNReal) ^ 2 * covarianceNorm K) ≤
        1 / ((n : ENNReal) ^ 2 * poincare K) ∧
      ENNReal.ofReal c / ((n : ENNReal) ^ 3 * poincare K) ≤ coordinateGap K b ∧
      ENNReal.ofReal c / ((n : ENNReal) ^ 3 * covarianceNorm K) ≤
        1 / ((n : ENNReal) ^ 3 * poincare K) := by sorry

end HitRunGaps.Spectral
