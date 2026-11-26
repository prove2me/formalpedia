-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneIntegerIncrementBudget
-- name    : Kyprianou.Ch05.monotoneIntegerIncrementBudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:34.803591+00:00
-- url     : https://prove2.me/theorems/42e2ab03-bcff-52a3-a105-8a5bc16f688e
-- title:
--   Successive increments of a monotone integer sequence in [0,1] have sum at most one
-- statement:
--   Successive increments of a monotone integer sequence in [0,1] have sum at most one
-- source:
--   Kyprianou (2006), Lemma 5.5, renewal-tail estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.monotoneIntegerIncrementBudget
    (f : Int → Real) (hm : Monotone f)
    (hn : ∀ k, 0 ≤ f k) (hb : ∀ k, f k ≤ 1) :
    Summable (fun k : Int => f (k+1)-f k) ∧
      (∑' k : Int, (f (k+1)-f k)) ≤ 1 := by sorry
