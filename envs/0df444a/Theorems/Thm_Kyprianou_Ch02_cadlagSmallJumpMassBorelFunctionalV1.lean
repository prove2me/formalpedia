-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagSmallJumpMassBorelFunctionalV1
-- name    : Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:18:59.010719+00:00
-- url     : https://prove2.me/theorems/ceb21841-d022-4142-866e-4de3998b0b5a
-- title:
--   Measurable functional representing the total absolute small-jump mass of each cadlag real path
-- statement:
--   For every compact nonnegative time horizon, construct a measurable functional on real-valued time-path product space that agrees with the extended nonnegative total absolute size of all positive-time jumps no larger than one for every cadlag path. Use public proved generic cadlag jump-time enumeration and measurable deduplicated weighted mark series; the missing deterministic step identifies the weighted sum over actual jump times with the enumerated series, accounting for zero jumps and strictly positive times. No probability measure or Levy process is needed.
-- source:
--   Proved public Avram generic cadlag weighted enumeration, source UUID e2bed90b-591b-4274-ac67-2df0882b298f and measurable series UUID 37d36ef8-8cd7-45f8-9760-7f03c4ea6366; Kyprianou Ch2 Lemma 2.12 path jump function.

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1
    (T : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ (Y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          ENNReal.ofReal
            (if |Y (s : ℝ≥0) -
                 Function.leftLim Y (s : ℝ≥0)| ≤ (1 : ℝ)
             then |Y (s : ℝ≥0) -
                    Function.leftLim Y (s : ℝ≥0)|
             else 0) := by
  sorry
