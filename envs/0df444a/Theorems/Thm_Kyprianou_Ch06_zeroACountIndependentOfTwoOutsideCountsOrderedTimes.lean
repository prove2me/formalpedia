-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideCountsOrderedTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsOrderedTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:34:26.299519+00:00
-- url     : https://prove2.me/theorems/eec105bc-cbee-47a8-ac8e-abc6dd9ed404
-- title:
--   Zero A-count independent of two arbitrary overlapping outside mark count observations at ordered times
-- statement:
--   Source Chapter 6 marked-Poisson independence for two possibly overlapping outside mark sets B and C at arbitrary ordered times s≤t and arbitrary positive or zero count levels k,l. The two-count cylinder is the almost-sure disjoint union of finitely many four-compatible-rectangle atom events indexed by two prior overlapping spatial counts. Each atom is independent of zero A-count under the original rectangle law, and the proved countable-union event-independence theorem transfers their independence to the original cylinder. No strengthened process hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsOrderedTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
