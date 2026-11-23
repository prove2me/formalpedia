-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_hermite_expansion
-- name    : GrothendieckLB.Supplement.cq_gaussian_hermite_expansion
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T18:29:40.381554+00:00
-- url     : https://prove2.me/theorems/7e310387-2b85-47d7-bc77-7d4200278522
-- title:
--   Mehler expansion for the correlation of the cubic–quintic partitions
-- statement:
--   For every choice of the three real parameters and every real $t$ of absolute value less than one, the correlation has the absolutely convergent Hermite expansion
--   $$H(t)=\frac{\pi}{2}\sum_{a,b\ge 0}A_{a,b}^2\rho(t)^a(-t)^b.$$
--   Each Gaussian Hermite coefficient of the threshold satisfies $|A_{a,b}|\le 1$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Theorem 5.1, equations (14)–(15).

import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqA

namespace GrothendieckLB.Supplement

theorem cq_gaussian_hermite_expansion (η s₃ s₅ : ℝ) :
    (∀ t : ℝ, |t| < 1 → HasSum (fun p : ℕ × ℕ =>
       Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2)^2 * ((cqRhoPoly s₃ s₅).eval t)^p.1 * (-t)^p.2)
       (cqCorr η s₃ s₅ t)) ∧
    (∀ a b : ℕ, |cqA η s₃ s₅ a b| ≤ 1) := by sorry

end GrothendieckLB.Supplement
