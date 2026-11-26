-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCutoffTailIntegrable
-- name    : Kyprianou.Ch05.renewalCutoffTailIntegrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:55:49.779838+00:00
-- url     : https://prove2.me/theorems/63aa9444-1c5d-4cfa-838c-99c699bc30d6
-- title:
--   Finite first moment implies integrability of the cutoff renewal tail
-- statement:
--   Finite first moment implies integrability of the cutoff renewal tail
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalCutoffTailIntegrable
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hInt : Integrable (fun z : Real => z) F)
    (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    Integrable (fun t : Real => if y < t then (F (Set.Ioi (t + u))).toReal else 0) := by sorry
