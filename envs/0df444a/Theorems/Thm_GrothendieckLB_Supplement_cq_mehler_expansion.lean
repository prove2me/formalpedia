-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_mehler_expansion
-- name    : GrothendieckLB.Supplement.cq_mehler_expansion
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T18:16:56.283054+00:00
-- url     : https://prove2.me/theorems/6afb307c-b5d0-4996-a861-3dbaab166b72
-- title:
--   Integrated two-coordinate Mehler expansion for the cubic–quintic signs
-- statement:
--   For arbitrary real parameters the normalized Gaussian Hermite coefficients of the cubic threshold sign have absolute value at most one. At every real correlation strictly between −1 and 1, the two-coordinate Gaussian expectation is the absolutely summable Mehler expansion. This is the analytic part of equation (15), before extracting its finite Taylor coefficients. The normalization follows from one-dimensional Hermite orthogonality and the expansion follows by integrating the product of the two one-dimensional Mehler kernels.
-- source:
--   Saha et al., arXiv:2608.11158, Theorem 5.1, equation (15).

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_cqA
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

theorem cq_mehler_expansion (η s₃ s₅ : ℝ) :
    (∀ a b : ℕ, |cqA η s₃ s₅ a b| ≤ 1) ∧
    (∀ t : ℝ, |t| < 1 →
      HasSum (fun p : ℕ × ℕ => Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2) ^ 2 *
        ((cqRhoPoly s₃ s₅).eval t) ^ p.1 * (-t) ^ p.2) (cqCorr η s₃ s₅ t)) := by sorry

end GrothendieckLB.Supplement
