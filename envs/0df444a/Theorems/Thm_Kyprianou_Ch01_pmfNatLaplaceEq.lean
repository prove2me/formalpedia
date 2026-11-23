-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfNatLaplaceEq
-- name    : Kyprianou.Ch01.pmfNatLaplaceEq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:15:01.452804+00:00
-- url     : https://prove2.me/theorems/5c013752-0e7f-44e4-9234-cbc27da22dfe
-- title:
--   Injectivity of the natural-number PMF Laplace generating series
-- statement:
--   For arbitrary probability mass functions on nonnegative integers, equality of their exponentially weighted generating sums at every positive real Laplace parameter implies equality of the mass functions. Use uniqueness of power-series coefficients or uniqueness of Laplace transforms of finite discrete measures; no moment assumption is needed.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, uniqueness of discrete branching transition probabilities from their Laplace transforms

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfNatLaplaceEq
    (p r : PMF ℕ)
    (hLaplace : ∀ (q : ℝ), 0 < q →
      (∑' n : ℕ, (p n).toReal * Real.exp (-q * (n : ℝ))) =
      (∑' n : ℕ, (r n).toReal * Real.exp (-q * (n : ℝ)))) :
    p = r := by
  sorry
