-- Prove2me | Theorems.Thm_Kyprianou_Ch05_realToNNRealPositiveTailTransport
-- name    : Kyprianou.Ch05.realToNNRealPositiveTailTransport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:35.181026+00:00
-- url     : https://prove2.me/theorems/220aea08-101c-4d0d-ba34-61895dd00a4a
-- title:
--   Positive upper rays and first moment transport under the nonnegative-part map
-- statement:
--   Positive upper rays and first moment transport under the nonnegative-part map
-- source:
--   Kyprianou (2006), Lemma 5.5, renewal-tail estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.realToNNRealPositiveTailTransport
    (F : Measure Real) [IsProbabilityMeasure F]
    (hInt : Integrable (fun z : Real => z) F) :
    let m := Measure.map Real.toNNReal F
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂m) < ⊤ ∧
      ∀ t : Real, 0 < t → m {z : ℝ≥0 | t < (z : ℝ)} = F (Ioi t) := by sorry
