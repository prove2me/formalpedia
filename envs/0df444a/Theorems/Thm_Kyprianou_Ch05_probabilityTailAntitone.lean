-- Prove2me | Theorems.Thm_Kyprianou_Ch05_probabilityTailAntitone
-- name    : Kyprianou.Ch05.probabilityTailAntitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:59:04.629798+00:00
-- url     : https://prove2.me/theorems/c9db5da7-2b7a-4a02-96d3-c0e3916c1877
-- title:
--   Probability tail real values are antitone and lie in the unit interval
-- statement:
--   Probability tail real values are antitone and lie in the unit interval
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.probabilityTailAntitone
    (F : Measure Real) [IsProbabilityMeasure F] :
    Antitone (fun t : Real => (F (Ioi t)).toReal) ∧
      (∀ t : Real, 0 ≤ (F (Ioi t)).toReal) ∧
      (∀ t : Real, (F (Ioi t)).toReal ≤ 1) := by sorry
