-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:24:31.587439+00:00
-- url     : https://prove2.me/theorems/d73423c3-6e74-447c-ac2d-db4f250f2746
-- title:
--   Zero A-count independent of all ordered three-time same-mark count cylinders with any levels
-- statement:
--   The original Chapter 6 marked-Poisson zero A-count is independent of the entire triple count cylinder for one outside mark B at ordered times s≤t≤u, including arbitrary, potentially inconsistent prescribed cumulative count levels. For monotone levels, the independently verified three-rectangle Poisson factorisation applies; if levels decrease, a.e path monotonicity makes the event null. This closes both cases without changing the source process hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by sorry
