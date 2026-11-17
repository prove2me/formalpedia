-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- name    : Kyprianou.Ch06.zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:30:13.991353+00:00
-- url     : https://prove2.me/theorems/d410e1ee-bdd9-41a3-8ed9-84ace5ffecdd
-- title:
--   Zero A-count independent of arbitrary finite count cylinders using two outside mark/time coordinates
-- statement:
--   Full source Chapter 6 finite-dimensional marked Poisson restriction independence when observations belong to either of two arbitrary outside-A mark/time coordinates (s,B) or (t,C), with arbitrary finite dimension, repetitions, inconsistent level values and possibly overlapping B,C. Its count vector is an almost-sure deterministic function of the two count values. Apply the already Proved arbitrary-overlap two-count zero A-factorisation and proved countably-valued statistic independence transfer. No process or mark assumptions are strengthened.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (m : Nat) (r s t : NNReal)
    (times : Fin m → NNReal) (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      (times i = s ∧ marks i = B) ∨
      (times i = t ∧ marks i = C))
    (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega (times i) (marks i) = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (marks i) = levels i} := by sorry
