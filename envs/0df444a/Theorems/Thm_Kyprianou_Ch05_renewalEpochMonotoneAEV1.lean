-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalEpochMonotoneAEV1
-- name    : Kyprianou.Ch05.renewalEpochMonotoneAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:00:02.99327+00:00
-- url     : https://prove2.me/theorems/e49666d9-4d26-46ca-82b4-566270f123cd
-- title:
--   Renewal epochs are nonnegative and nondecreasing almost surely
-- statement:
--   Renewal epochs are nonnegative and nondecreasing almost surely
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalEpochMonotoneAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F) :
    ∀ᵐ w ∂P, Monotone (fun n => renewalEpoch Z n w) := by
  sorry
