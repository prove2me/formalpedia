-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailJointKernelENN
-- name    : Kyprianou.Ch05.renewalTailJointKernelENN
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:58:54.555682+00:00
-- url     : https://prove2.me/theorems/8af6055e-3d8f-411e-a657-f837bc828a99
-- title:
--   Positive overshoot and undershoot tails equal the joint renewal kernel
-- statement:
--   Positive overshoot and undershoot tails equal the joint renewal kernel
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalTailJointKernelENN
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x u y : Real) (hx : 0 < x) (hu : 0 < u) :
    P {w : Omega | u < renewalOvershoot Z x w ∧ y < renewalUndershoot Z x w} =
      renewalJointKernel (renewalMeasure F) F x (Ioi u) (Ioi y) := by sorry
