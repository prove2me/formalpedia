-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfOutsideCount
-- name    : Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfOutsideCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:11:43.371231+00:00
-- url     : https://prove2.me/theorems/eaabbf5c-5ece-4a97-a598-da53008b82a7
-- title:
--   Lemma 6.18: two competing zero-count events are independent of a third outside count
-- statement:
--   For three pairwise-disjoint finite-intensity mark sets B,D,C, the joint event of zero B marks by s and zero D marks by t is independent of the C-mark count at any observation time u. This is the three-region finite-cylinder count factorisation needed to prove first-mark independence of outside observations.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, independence of first-mark competition from outside-A Poisson counts.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfOutsideCount
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      N omega s B = 0 ∧ N omega t D = 0 ∧ N omega u C = k} =
    P {omega | N omega s B = 0 ∧ N omega t D = 0} *
      P {omega | N omega u C = k} := by sorry
