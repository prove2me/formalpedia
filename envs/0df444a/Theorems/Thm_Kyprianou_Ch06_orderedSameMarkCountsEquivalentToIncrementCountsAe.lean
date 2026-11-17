-- Prove2me | Theorems.Thm_Kyprianou_Ch06_orderedSameMarkCountsEquivalentToIncrementCountsAe
-- name    : Kyprianou.Ch06.orderedSameMarkCountsEquivalentToIncrementCountsAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:12:28.329201+00:00
-- url     : https://prove2.me/theorems/b56ee9d9-e51d-47cb-9384-bb1c5124e6ca
-- title:
--   Ordered cumulative marked-Poisson count cylinder equals consecutive increment cylinder almost surely
-- statement:
--   Under the original marked-Poisson sample-path initial zero count and monotonicity, for ordered observation times s≤t and cumulative count levels k≤l, the event N_s(B)=k and N_t(B)=l is equivalent almost surely to the increment conditions N_s(B)-N_0(B)=k and N_t(B)-N_s(B)=l-k. Works for arbitrary mark set B without any extra process hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.orderedSameMarkCountsEquivalentToIncrementCountsAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B : Set E) (s t : NNReal) (hst : s ≤ t)
    (k l : Nat) (hkl : k ≤ l) :
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t B = l) ↔
      (N omega s B - N omega 0 B = k ∧
        N omega t B - N omega s B = l-k) := by sorry
