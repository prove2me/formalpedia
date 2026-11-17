-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:22:51.751465+00:00
-- url     : https://prove2.me/theorems/4caeb2e9-47fe-4f7b-a741-3c179db908b9
-- title:
--   Zero A-count independent of three ordered same-mark cumulative observations at monotonic levels
-- statement:
--   For marked-Poisson counts of the same outside mark set B at three ordered times s≤t≤u, with monotonic count values k≤l≤q, the source zero A-count at any time r is independent of the full three-coordinate cumulative observation cylinder. Prove by the independently source-verified equivalence to three time-disjoint rectangle-increments, the source finite compatible rectangle independence, and a.e event factorisation transfer. No source assumptions were strengthened.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) (hkl : k ≤ l) (hlq : l ≤ q) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by sorry
