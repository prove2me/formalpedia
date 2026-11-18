-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsIndependentOfOneOutsideCount
-- name    : Kyprianou.Ch06.twoFirstArrivalsIndependentOfOneOutsideCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:23:46.789858+00:00
-- url     : https://prove2.me/theorems/692bdfd5-d132-4a14-aff3-d23206290d34
-- title:
--   Lemma 6.18: joint first arrival survival of two disjoint mark sets independent of one outside count
-- statement:
--   For three pairwise-disjoint finite-intensity mark regions B,D,C, the joint event that first B and D arrivals exceed their respective times is independent of the C-mark count at any time. This is the one-cylinder first-mark competition/outside process independence needed before the finite overlapping outside-count vector extension.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, independence of the first A-mark process and outside-A marked point process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsAndOutsideCountJointZeroIdentity
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfOutsideCount
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoFirstArrivalsIndependentOfOneOutsideCount
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D}) ∧
      N omega u C = k} =
    P {omega | (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D})} *
      P {omega | N omega u C = k} := by sorry
