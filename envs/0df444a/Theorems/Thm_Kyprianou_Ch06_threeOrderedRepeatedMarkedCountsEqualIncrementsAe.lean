-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeOrderedRepeatedMarkedCountsEqualIncrementsAe
-- name    : Kyprianou.Ch06.threeOrderedRepeatedMarkedCountsEqualIncrementsAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:21:04.275902+00:00
-- url     : https://prove2.me/theorems/9b1cc3ac-ea81-4def-92bb-1345e39bcaa2
-- title:
--   Three ordered cumulative marked Poisson counts coincide a.e. with consecutive increment counts
-- statement:
--   Under the exact Chapter 6 marked-Poisson a.e sample-path initial-zero and monotonicity laws, an ordered triple of cumulative counts of the same mark set at s≤t≤u and nondecreasing count levels k≤l≤q is equivalent almost surely to the triple of consecutive rectangle-increment counts on [0,s], (s,t] and (t,u]. This supplies a genuine 3-coordinate source count-cylinder decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.threeOrderedRepeatedMarkedCountsEqualIncrementsAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B : Set E) (s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) (hkl : k ≤ l) (hlq : l ≤ q) :
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t B = l ∧
        N omega u B = q) ↔
      (N omega s B-N omega 0 B = k ∧
        N omega t B-N omega s B = l-k ∧
        N omega u B-N omega t B = q-l) := by sorry
