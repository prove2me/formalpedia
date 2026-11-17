-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFiniteThreeOutsideMarksSameTime
-- name    : Kyprianou.Ch06.zeroACountIndependentOfFiniteThreeOutsideMarksSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:47:52.371186+00:00
-- url     : https://prove2.me/theorems/d6833b22-9c65-4f60-bf08-9b0e58650bdd
-- title:
--   Zero A-count independent of any finite count vector selected from three overlapping outside marks at one common time
-- statement:
--   For arbitrary finite dimension m, repeated or inconsistent count levels, and three possibly overlapping outside-A mark sets B,C,D measured at a common time u, the entire count vector is a deterministic function of the three original count coordinates. The already verified full three-mark joint count factorisation and independently proved countable-statistic independence transfer establish the exact source Poisson factorisation without strengthened hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfFiniteThreeOutsideMarksSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C D : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (m : Nat) (r u : NNReal)
    (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      marks i = B ∨ marks i = C ∨ marks i = D)
    (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega u (marks i) = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m,
        N omega u (marks i) = levels i} := by sorry
