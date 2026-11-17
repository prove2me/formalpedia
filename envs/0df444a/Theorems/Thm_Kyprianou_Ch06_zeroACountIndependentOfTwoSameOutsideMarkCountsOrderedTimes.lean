-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoSameOutsideMarkCountsOrderedTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoSameOutsideMarkCountsOrderedTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:09:54.34926+00:00
-- url     : https://prove2.me/theorems/c3b409b4-0b52-4f4e-8482-fedc1cf876fc
-- title:
--   Zero A-count independent of two observations of the same outside B mark set at ordered times
-- statement:
--   Under the original marked Poisson rectangle law, the event that A has zero count at arbitrary time r is independent of two nondecreasing B-count observations N_s(B)=k and N_t(B)=l at ordered times s≤t for any disjoint finite-intensity mark sets A,B. When k≤l, the observed B pair is almost surely equivalent to two consecutive B-increment constraints and the independently proved three-rectangle factorisation applies. For k>l, B monotonicity makes the cylinder almost surely empty, so the same identity follows. Original source process and all time/count assumptions are preserved.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoSameOutsideMarkCountsOrderedTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t B = l} := by sorry
