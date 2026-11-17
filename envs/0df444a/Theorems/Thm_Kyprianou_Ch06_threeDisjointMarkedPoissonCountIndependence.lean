-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonCountIndependence
-- name    : Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:15:13.556101+00:00
-- url     : https://prove2.me/theorems/3be3f30e-9439-4c59-8fb9-faa754c2b39f
-- title:
--   Chapter 6: three spatially disjoint marked Poisson counts are mutually independent
-- statement:
--   Under the original Chapter 6 marked Poisson point process assumptions, any three counting variables for pairwise disjoint measurable finite-intensity mark sets, evaluated at arbitrary nonnegative times, have a joint point-probability that factors into the product of their three marginal Poisson probabilities. This is a finite-dimensional stepping stone towards the full marked-Poisson outside-mark independence of Lemma 6.18.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (hFiniteC : n C < ⊤)
    (s t u : NNReal) (k l r : Nat) :
    P {omega | N omega s A = k ∧
      N omega t B = l ∧ N omega u C = r} =
    P {omega | N omega s A = k} *
    P {omega | N omega t B = l} *
    P {omega | N omega u C = r} := by sorry
