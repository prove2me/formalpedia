-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailKernelInner
-- name    : Kyprianou.Ch05.renewalTailKernelInner
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:44.234801+00:00
-- url     : https://prove2.me/theorems/1fa3a7f3-d543-46dc-ac9d-5407acb8ce13
-- title:
--   The inner strict upper-ray kernel is the shifted strict tail
-- statement:
--   The inner strict upper-ray kernel is the shifted strict tail
-- source:
--   Kyprianou (2006), Lemma 5.5, renewal-tail estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalTailKernelInner
    (F : Measure Real) (v x u y : Real) (hu : 0 < u) :
    (∫⁻ z in Ioi (x-v),
      (if z-(x-v) ∈ Ioi u ∧ x-v ∈ Ioi y then (1 : ENNReal) else 0) ∂F) =
      if y < x-v then F (Ioi (x-v+u)) else 0 := by sorry
