-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonCountMonotoneSpaceTimeAe
-- name    : Kyprianou.Ch06.markedPoissonCountMonotoneSpaceTimeAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:51:27.788914+00:00
-- url     : https://prove2.me/theorems/1c2b81d6-937e-477e-ba60-b70e5b5cb539
-- title:
--   Chapter 6 marked Poisson count is monotone in mark set and time almost surely
-- statement:
--   Under the source marked Poisson sample-path finite additivity and time monotonicity assumptions, if B⊆C and s≤t then N_s(B)≤N_t(C) almost surely. Derive spatial monotonicity from the disjoint partition C=B∪(C\B), and compose with the original temporal monotonicity. This source-faithful lemma is useful for nested mark count cylinder constraints.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonCountMonotoneSpaceTimeAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hBC : B ⊆ C)
    (s t : NNReal) (hst : s ≤ t) :
    ∀ᵐ omega ∂P, N omega s B ≤ N omega t C := by sorry
