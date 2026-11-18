-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonArrivalUnionMin
-- name    : Kyprianou.Ch06.firstMarkedPoissonArrivalUnionMin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:49:08.309181+00:00
-- url     : https://prove2.me/theorems/5b6f91f3-d8f9-4011-9fde-a363aa6ea031
-- title:
--   Lemma 6.18: first arrival into disjoint marked-Poisson union is minimum of arrival times
-- statement:
--   For a marked-Poisson counting process and any two disjoint mark regions B,D, the first strictly positive arrival time into B∪D (as a WithTop NNReal infimum) equals the minimum of the respective B and D first-arrival times, almost surely. The source is the pathwise count-additivity clause of the published marked-Poisson definition, not an extra stochastic hypothesis. This is the exact time decomposition for first-mark competing intensities in Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18, printed pp.160–161, decomposition of first A-mark into the competing C∩A and A∖C first arrivals.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkedPoissonArrivalUnionMin
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hDisj : Disjoint B D) :
    ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (B ∪ D)}) =
      min
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t B}))
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t D})) := by sorry
