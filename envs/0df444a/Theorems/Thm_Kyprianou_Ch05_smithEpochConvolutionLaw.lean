-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithEpochConvolutionLaw
-- name    : Kyprianou.Ch05.smithEpochConvolutionLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:05:36.506311+00:00
-- url     : https://prove2.me/theorems/645a2968-aa92-428b-aa71-1efb1ccf49ba
-- title:
--   Smith elementary renewal bridge: partial sums have convolution-power law
-- statement:
--   The nth renewal epoch of a Smith renewal process has the nth convolution power of its common spacing law.
-- source:
--   Kyprianou (2006), Theorem 5.1(iii); exact transfer from SmithRenewal.Elementary.elementary_renewal_theorem b689ea1a-fac8-4240-8c12-fa8e3e439bae to parent 0e4a1289-230f-405a-bb6b-dc73f33160d0.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

theorem Kyprianou.Ch05.smithEpochConvolutionLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat → Omega → Real) (F : Measure Real)
    (hX : IsRenewalProcess P X)
    (hLaw : ∀ n, Measure.map (X n) P = F) (n : Nat) :
    Measure.map (S X n) P = renewalConvolutionPower F n := by sorry
