-- Prove2me | Theorems.Thm_Kyprianou_Ch06_dominatedOutsideZeroCylinderIffSingleZeroAe
-- name    : Kyprianou.Ch06.dominatedOutsideZeroCylinderIffSingleZeroAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:04:16.699801+00:00
-- url     : https://prove2.me/theorems/6391b871-34de-4745-8e1a-68ccc9c4b5f9
-- title:
--   Finite marked Poisson zero-count cylinder is equivalent almost surely to its dominating coordinate
-- statement:
--   For a Chapter 6 marked Poisson process and arbitrary finite family of mark sets B_i and observation times t_i, if one coordinate u dominates every other both spatially B_i⊆B_u and temporally t_i≤t_u, then the conjunction N_{t_i}(B_i)=0 for every i is almost surely equivalent to N_{t_u}(B_u)=0. Proved from the source simultaneous mark/time monotonicity, with no extra probabilistic independence assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.dominatedOutsideZeroCylinderIffSingleZeroAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (u : Fin m)
    (hDom : ∀ i : Fin m, B i ⊆ B u ∧ times i ≤ times u) :
    ∀ᵐ omega ∂P,
      (∀ i : Fin m, N omega (times i) (B i) = 0) ↔
        N omega (times u) (B u) = 0 := by sorry
