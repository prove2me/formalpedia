-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalJointKernelTailENN
-- name    : Kyprianou.Ch05.renewalJointKernelTailENN
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:23.909808+00:00
-- url     : https://prove2.me/theorems/4ed3942c-50ae-557d-b618-11dc69cb6ab9
-- title:
--   Joint renewal kernel equals the extended-real tail convolution
-- statement:
--   Joint renewal kernel equals the extended-real tail convolution.
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalJointKernelTailENN
    (V F : Measure Real) (x u y : Real) (hu : 0 < u) :
    renewalJointKernel V F x (Ioi u) (Ioi y) =
      ∫⁻ v in Icc (0 : Real) x, (if y < x-v then F (Ioi (x-v+u)) else 0) ∂V := by sorry
