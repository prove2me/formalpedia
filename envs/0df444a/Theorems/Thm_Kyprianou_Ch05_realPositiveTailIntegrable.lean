-- Prove2me | Theorems.Thm_Kyprianou_Ch05_realPositiveTailIntegrable
-- name    : Kyprianou.Ch05.realPositiveTailIntegrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:58:52.546993+00:00
-- url     : https://prove2.me/theorems/1cbf82c0-b08c-4ed7-85a9-f7e2a1fefb08
-- title:
--   Real measure with integrable coordinate has integrable strict positive tail
-- statement:
--   Real measure with integrable coordinate has integrable strict positive tail
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.realPositiveTailIntegrable
    (F : Measure Real) [IsProbabilityMeasure F]
    (hInt : Integrable (fun z : Real => z) F) :
    IntegrableOn (fun t : Real => (F (Ioi t)).toReal) (Ioi (0 : Real)) := by sorry
