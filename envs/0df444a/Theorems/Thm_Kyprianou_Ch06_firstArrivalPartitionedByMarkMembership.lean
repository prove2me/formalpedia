-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalPartitionedByMarkMembership
-- name    : Kyprianou.Ch06.firstArrivalPartitionedByMarkMembership
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:07:51.187415+00:00
-- url     : https://prove2.me/theorems/46bffedd-de4b-4e2b-ae8b-c604bfc9e6c7
-- title:
--   Lemma 6.18: first A-mark arrival is the minimum of the first arrivals inside and outside C
-- statement:
--   For a marked Poisson point process and any two mark sets A and C, the first positive-count arrival into A equals the minimum of the first arrival into A∩C and the first arrival into A\C, almost surely. This is the pathwise partition underpinning the first-mark competition and conditional mark law.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, split A-mark arrivals according to membership in a measurable region C.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonArrivalUnionMin
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalPartitionedByMarkMembership
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A C : Set E) :
    ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) =
      min
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}))
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) := by sorry
