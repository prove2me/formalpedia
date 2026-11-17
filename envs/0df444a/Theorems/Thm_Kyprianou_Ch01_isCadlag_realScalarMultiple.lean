-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isCadlag_realScalarMultiple
-- name    : Kyprianou.Ch01.isCadlag_realScalarMultiple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:21:44.485667+00:00
-- url     : https://prove2.me/theorems/012dc272-acc0-4d3e-8c0b-82090ae07b1d
-- title:
--   Real scalar multiplication preserves the full LeanLevy càdlàg path condition
-- statement:
--   Every càdlàg path on nonnegative time remains càdlàg when multiplied by any fixed real scalar. The right-continuous-within and left-limit conditions are both preserved by the continuous scalar multiplication map, and the proof is the direct composition of the pinned continuous-within and Filter.Tendsto.const_mul facts. This supports the scaled Brownian component of the positive Gaussian Lévy process.
-- source:
--   LeanLevy_Processes_Cadlag; Kyprianou (2006), Chapter 1 Lévy process sample-path regularity.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open ProbabilityTheory Set Filter
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isCadlag_realScalarMultiple
    (c : ℝ) (f : ℝ≥0 → ℝ)
    (h : IsCadlag f) :
    IsCadlag (fun t => c * f t) := by
  sorry
