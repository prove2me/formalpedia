-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
-- name    : Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:08:18.669019+00:00
-- url     : https://prove2.me/theorems/ff12974d-be29-406f-8e87-5323683b841b
-- title:
--   Chapter 6 disjoint marked Poisson spatial count events are independent
-- statement:
--   For any two measurable disjoint finite-intensity mark sets, the marked Poisson counting variables at arbitrary deterministic times have independent point probabilities. This follows from the genuine independent two-rectangle law, the almost-sure zero initial counts, and the separately Proved Poisson marginal count laws, and contributes to the outside-mark independence component of Chapter 6 Lemma 6.18.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t B = l} =
      P {omega | N omega s A = k} *
      P {omega | N omega t B = l} := by sorry
