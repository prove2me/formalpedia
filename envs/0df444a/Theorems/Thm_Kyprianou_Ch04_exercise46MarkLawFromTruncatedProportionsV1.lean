-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MarkLawFromTruncatedProportionsV1
-- name    : Kyprianou.Ch04.exercise46MarkLawFromTruncatedProportionsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:09.810844+00:00
-- url     : https://prove2.me/theorems/c14627ef-14b6-4fb9-af05-d0b7739c0c23
-- title:
--   First-mark law from finite-horizon proportions
-- statement:
--   Pass to the increasing union of finite-horizon first-arrival events; the arrival is finite almost surely.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MarkLawFromTruncatedProportionsV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (eta : Measure E) (J : Omega → E) (hJ : AEMeasurable J P)
    (D : Nat → Set Omega) (hD : Monotone D)
    (hFull : (⋃ n, D n) =ᵐ[P] (univ : Set Omega))
    (hProportion : ∀ n B, MeasurableSet B →
      P (D n ∩ J ⁻¹' B) = P (D n) * eta B) :
    P.map J = eta := by
  sorry
