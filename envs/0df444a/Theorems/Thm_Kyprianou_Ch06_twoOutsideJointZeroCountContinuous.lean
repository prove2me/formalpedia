-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoOutsideJointZeroCountContinuous
-- name    : Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:35:35.833199+00:00
-- url     : https://prove2.me/theorems/7accd5ba-5e01-4d39-a287-f7ad833e9a84
-- title:
--   Chapter 6 marked Poisson joint zero-count probability with two disjoint outside mark counts varies continuously in time
-- statement:
--   Chapter 6 marked Poisson joint zero-count probability with two disjoint outside mark counts varies continuously in time. The first theorem follows from the genuine marked-Poisson three-rectangle joint distribution, independent outside counts and continuous exponential zero-count law. The second uses the first-arrival joint-event sandwich and the same spatially independent count laws. The full original positive time and mark intensity assumptions are retained, including arbitrary deterministic times and count levels.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    ContinuousAt (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k ∧
        N omega v C = l}) t := by sorry
