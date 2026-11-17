-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:26:07.820728+00:00
-- url     : https://prove2.me/theorems/cd06760a-30a3-4f7e-8106-a30fb7c9bfc9
-- title:
--   Zero A-count independent of three repeated outside marks at all observation-time orders
-- statement:
--   Source Chapter 6 marked-Poisson zero A-count is independent of the three-coordinate cumulative count cylinder of the same outside mark B at arbitrary unsorted observation times and arbitrary count values. Exhaust all six relative time orderings and invoke the exact proved ordered triple cylinder factorisation with the corresponding permutation of count levels, using conjunction commutativity to reassemble the original observation event.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by sorry
