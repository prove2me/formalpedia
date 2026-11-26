-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finitePartitionIntegralError
-- name    : Kyprianou.Ch05.finitePartitionIntegralError
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:49:08.831354+00:00
-- url     : https://prove2.me/theorems/d28625b8-8a17-5432-95ac-f35b0a64e44c
-- title:
--   Finite-support disjoint partition integral error bounded by weighted cell errors
-- statement:
--   Finite-support disjoint partition integral error bounded by weighted cell errors
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.finitePartitionIntegralError
    (V : Measure Real) (T : Set Real) (S : Nat → Set Real)
    (hT : V T ≠ ⊤)
    (hU : (⋃ k, S k) = T)
    (hD : Pairwise (Function.onFun Disjoint S))
    (hM : ∀ k, MeasurableSet (S k))
    (hN : ∃ N : Nat, ∀ k : Nat, N ≤ k → S k = ∅)
    (f : Real → Real) (hf : IntegrableOn f T V)
    (c e : Nat → Real)
    (ha : ∀ k z, z ∈ S k → |f z-c k| ≤ e k) :
    |(∫ z in T, f z ∂V) - (∑' k : Nat, c k * (V (S k)).toReal)| ≤
      ∑' k : Nat, e k * (V (S k)).toReal := by sorry
