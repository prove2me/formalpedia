-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfRepeatedOutsideMarkTimeVector
-- name    : Kyprianou.Ch06.zeroACountIndependentOfRepeatedOutsideMarkTimeVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:13:32.538426+00:00
-- url     : https://prove2.me/theorems/f1b8ba6a-8b56-45e7-b07a-4a7f38035bcb
-- title:
--   Zero A-count independent of any finite repeated outside-mark and observation-time count vector
-- statement:
--   A source-faithful finite-dimensional marked-Poisson cylinder identity with all outside marks observed as the same B at the same deterministic time u but with arbitrary finite numbers and count levels. The first arrival zero A-count is independent of the entire observed count vector. Prove using independently Proved two-coordinate full overlapping mark factorisation, then transfer of event independence through the countably-valued deterministic repeated-count vector. Handles inconsistent count levels correctly as a zero-probability event.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfRepeatedOutsideMarkTimeVector
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (m : Nat) (r u : NNReal) (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega u B = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m, N omega u B = levels i} := by sorry
