-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
-- name    : Kyprianou.Ch06.zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:10:47.216405+00:00
-- url     : https://prove2.me/theorems/8e0bff6f-6f92-4c75-9caf-4069f450a092
-- title:
--   Source three-rectangle Poisson product for zero A-count and two consecutive outside B increments
-- statement:
--   Instantiate exactly the original Chapter 6 finite-rectangle marked-Poisson law with three pairwise disjoint space-time rectangles: A between 0 and r, B between 0 and s, and B between s and t. The latter two rectangles are disjoint in time, and A is spatially disjoint from B. Their joint count probability, with zero A-count and arbitrary B-increment counts, is the product of their prescribed Poisson atom probabilities. No independent increment assumption beyond the original source marked-Poisson rectangle law is added.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} =
    ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
      (ProbabilityTheory.poissonMeasure (s * (n B).toNNReal) {k} *
        ProbabilityTheory.poissonMeasure ((t-s) * (n B).toNNReal) {l}) := by sorry
