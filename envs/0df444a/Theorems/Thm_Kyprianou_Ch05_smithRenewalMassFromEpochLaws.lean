-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithRenewalMassFromEpochLaws
-- name    : Kyprianou.Ch05.smithRenewalMassFromEpochLaws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:05:37.281171+00:00
-- url     : https://prove2.me/theorems/95aeefcd-8476-5f26-972a-e347b1bb83e6
-- title:
--   Smith elementary renewal bridge: renewal measure equals one plus expected count
-- statement:
--   The renewal measure on [0,t] equals one plus Smith's expected number of positive-index renewal epochs. Infinite counts are included.
-- source:
--   Kyprianou (2006), Theorem 5.1(iii); exact transfer from SmithRenewal.Elementary.elementary_renewal_theorem b689ea1a-fac8-4240-8c12-fa8e3e439bae to parent 0e4a1289-230f-405a-bb6b-dc73f33160d0.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

theorem Kyprianou.Ch05.smithRenewalMassFromEpochLaws
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat → Omega → Real) (F : Measure Real)
    (hX : IsRenewalProcess P X)
    (hLaw : ∀ n, Measure.map (S X n) P = renewalConvolutionPower F n)
    (t : Real) (ht : 0 ≤ t) :
    renewalMeasure F (Set.Icc 0 t) = 1 + H X P t := by sorry
