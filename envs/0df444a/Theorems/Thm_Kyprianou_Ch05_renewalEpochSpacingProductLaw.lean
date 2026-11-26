-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalEpochSpacingProductLaw
-- name    : Kyprianou.Ch05.renewalEpochSpacingProductLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:55:50.93566+00:00
-- url     : https://prove2.me/theorems/3bddf2ca-40c4-4b36-99b0-f09a0d09ff31
-- title:
--   Joint law of renewal epoch and next spacing equals convolution power times spacing law
-- statement:
--   Joint law of renewal epoch and next spacing equals convolution power times spacing law
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalEpochSpacingProductLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (n : Nat) :
    Measure.map (fun w => (renewalEpoch Z n w,Z n w)) P =
      (renewalConvolutionPower F n).prod F := by sorry
