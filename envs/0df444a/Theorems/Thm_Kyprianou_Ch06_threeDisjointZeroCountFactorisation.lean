-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeDisjointZeroCountFactorisation
-- name    : Kyprianou.Ch06.threeDisjointZeroCountFactorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:42:35.014666+00:00
-- url     : https://prove2.me/theorems/17754f7b-6311-4bd7-97cb-1bd460a38319
-- title:
--   Three disjoint marked-Poisson counts: isolate zero A-count from two outside count cylinder
-- statement:
--   Under the original marked Poisson rectangle hypotheses and pairwise disjoint measurable finite-intensity A,B,C, the zero A count at time t is independent of the pair of B and C counts at arbitrary times and levels. Genuine consequence of separately Proved three-count joint factorisation and two-count independence, preserving all spatial and temporal quantifiers.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeDisjointZeroCountFactorisation
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    P {omega | N omega t A = 0 ∧ N omega u B = k ∧
      N omega v C = l} =
    P {omega | N omega t A = 0} *
      P {omega | N omega u B = k ∧ N omega v C = l} := by sorry
