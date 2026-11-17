-- Prove2me | Theorems.Thm_Kyprianou_Ch06_orderedSameMarkCountCylinderNullIfDescending
-- name    : Kyprianou.Ch06.orderedSameMarkCountCylinderNullIfDescending
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:13:02.395301+00:00
-- url     : https://prove2.me/theorems/73a7e649-b48d-44d8-b867-95703b13c015
-- title:
--   Ordered cumulative Poisson count cylinder has zero probability if the later count decreases
-- statement:
--   From the original marked-Poisson almost-sure time monotonicity, a cumulative count N_s(B)=k followed at later time t≥s by a strictly smaller count N_t(B)=l<k is impossible almost surely. The corresponding event has probability zero for any mark set B, without additional stochastic or measurability hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.orderedSameMarkCountCylinderNullIfDescending
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B : Set E) (s t : NNReal) (hst : s ≤ t)
    (k l : Nat) (hkl : l < k) :
    P {omega | N omega s B = k ∧ N omega t B = l} = 0 := by sorry
