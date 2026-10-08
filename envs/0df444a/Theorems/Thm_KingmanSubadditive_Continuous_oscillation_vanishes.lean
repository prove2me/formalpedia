-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_oscillation_vanishes
-- name    : KingmanSubadditive.Continuous.oscillation_vanishes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:13.150797+00:00
-- url     : https://prove2.me/theorems/e0c3be04-9f59-4302-a681-a91c83c8993a
-- title:
--   (1.4.9) — normalized unit-interval oscillation vanishes
-- statement:
--   Let $x$ satisfy the hypotheses of Theorem 4. As $n$ tends to infinity through the positive integers,
--
--   $$
--   \frac{\Omega_{[n,n+1]}}{n}\longrightarrow0
--   \quad\text{almost surely and in mean}.
--   $$
--
--   This controls the variation between consecutive integer times needed to pass from the skeleton limit to the full continuous-time limit.
--
--   **Formalization Note** The oscillation is extended nonnegative. Convergence in mean is stated through its nonnegative integral; exceptional infinite values on a null set do not change the assertion.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 889–890, §1.4, proof of Theorem 4, (1.4.9)

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, §1.4, proof of Theorem 4, (1.4.9), pp. 889–890.
The oscillation on unit intervals, divided by the integer time, tends to
zero almost surely and in mean. `ENNReal` retains any infinite values on a
null set; the nonnegative integral expresses the mean. -/
theorem oscillation_vanishes {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal)) atTop (𝓝 0)) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal) ∂P) atTop (𝓝 0) := by sorry

end KingmanSubadditive.Continuous
