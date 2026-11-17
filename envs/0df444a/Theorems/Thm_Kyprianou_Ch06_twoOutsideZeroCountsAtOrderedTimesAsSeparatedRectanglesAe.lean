-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoOutsideZeroCountsAtOrderedTimesAsSeparatedRectanglesAe
-- name    : Kyprianou.Ch06.twoOutsideZeroCountsAtOrderedTimesAsSeparatedRectanglesAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:25:29.576197+00:00
-- url     : https://prove2.me/theorems/f9e8aa76-e4eb-4072-af30-44075d84a1ad
-- title:
--   Two possibly overlapping zero counts at ordered times equal separated space-time rectangle void events
-- statement:
--   Under the exact original marked-Poisson source sample-path additive and monotonic count laws, for arbitrary mark sets B and C and any ordered times s≤t, the two zero-count observations N_s(B)=0 and N_t(C)=0 are almost surely equivalent to two count constraints on compatible space-time rectangles: N_s(B∪C)=0 and the increment N_t(C)-N_s(C)=0. This uses no mark disjointness between B and C. The two transformed rectangles have disjoint time intervals, enabling the original Poisson finite-rectangle factorisation and first-arrival zero-count sandwich.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.twoOutsideZeroCountsAtOrderedTimesAsSeparatedRectanglesAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (s t : NNReal) (hst : s ≤ t) :
    ∀ᵐ omega ∂P,
      (N omega s B = 0 ∧ N omega t C = 0) ↔
      (N omega s (B ∪ C) = 0 ∧
       N omega t C - N omega s C = 0) := by sorry
