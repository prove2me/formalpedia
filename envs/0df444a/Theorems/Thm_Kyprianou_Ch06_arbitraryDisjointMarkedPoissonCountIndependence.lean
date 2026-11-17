-- Prove2me | Theorems.Thm_Kyprianou_Ch06_arbitraryDisjointMarkedPoissonCountIndependence
-- name    : Kyprianou.Ch06.arbitraryDisjointMarkedPoissonCountIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:57:19.993751+00:00
-- url     : https://prove2.me/theorems/bb86731b-7a76-4447-93ed-ee0009aa59fa
-- title:
--   General finite family of disjoint marked-Poisson count events has independent joint law
-- statement:
--   For the Chapter 6 original marked Poisson point process, any finite collection of pairwise disjoint measurable mark sets of finite intensity has jointly independent count variables at arbitrary deterministic observation times, even with differing times and count levels. This is the full finite-dimensional spatial independence consequence of the source IsMarkedPoissonPointProcess disjoint-rectangle axiom, proved by using start times zero, almost-sure zero initial counts and the independently Proved exact Poisson count marginals.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.arbitraryDisjointMarkedPoissonCountIndependence
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hDisj : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j)) :
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      ∏ i : Fin m,
        P {omega | N omega (times i) (B i) = counts i} := by sorry
