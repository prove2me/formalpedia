-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianAllPositiveLevelsFiniteAeV1
-- name    : Kyprianou.Ch01.inverseGaussianAllPositiveLevelsFiniteAeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:12:29.21393+00:00
-- url     : https://prove2.me/theorems/89ad7c76-3996-46b2-ae03-f68d6e8c4f58
-- title:
--   Simultaneously finite upper-passage times at every positive barrier, almost surely
-- statement:
--   For positive-drift Brownian motion, almost surely every positive barrier has finite strict first-upper-passage time simultaneously. Take the countable intersection of the already-proved scalar a.s. finiteness results at natural barriers and transfer finiteness downward to arbitrary real barrier using monotonicity.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.5, and countable monotone-barrier exhaustion.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianAllPositiveLevelsFiniteAeV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s →
      Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤ := by
  sorry
