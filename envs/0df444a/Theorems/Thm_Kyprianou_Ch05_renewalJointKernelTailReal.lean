-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalJointKernelTailReal
-- name    : Kyprianou.Ch05.renewalJointKernelTailReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:58:55.146456+00:00
-- url     : https://prove2.me/theorems/175eed6c-f070-4df6-8894-a18fa1ad8be1
-- title:
--   Strict upper ray joint renewal kernel equals the real tail convolution
-- statement:
--   Strict upper ray joint renewal kernel equals the real tail convolution
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalJointKernelTailReal
    (V F : Measure Real) [IsFiniteMeasure F]
    (x u y : Real) (hu : 0 < u) :
    (renewalJointKernel V F x (Ioi u) (Ioi y)).toReal =
      ∫ v in Icc (0 : Real) x,
        (if y < x-v then (F (Ioi (x-v+u))).toReal else 0) ∂V := by sorry
