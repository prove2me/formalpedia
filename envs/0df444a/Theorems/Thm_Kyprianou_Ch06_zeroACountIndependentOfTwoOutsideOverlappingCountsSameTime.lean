-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideOverlappingCountsSameTime
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideOverlappingCountsSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:18:33.285385+00:00
-- url     : https://prove2.me/theorems/2f810a49-9105-4fd1-ac96-a7b5268d2ad2
-- title:
--   Zero A-count independent of two overlapping outside mark counts at common observation time
-- statement:
--   Under exactly the original Chapter 6 marked Poisson finite-rectangle law, for arbitrary measurable finite-intensity marks A, B and C with A spatially disjoint from B and C, the event N_s(A)=0 is independent of the joint count observations N_t(B)=k and N_t(C)=l at a common observation time, even when B and C overlap and for arbitrary nonzero count levels. Source finite additivity partitions the overlapping cylinder into finitely many mutually exclusive disjoint-atom count events; three disjoint atom count independence yields independence from N_s(A) for each atom event; countable disjoint union measure additivity yields independence of the original overlapping cylinder. All original time, count and intensity quantifiers remain unchanged.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideOverlappingCountsSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t B = k ∧
      N omega t C = l} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t B = k ∧ N omega t C = l} := by sorry
