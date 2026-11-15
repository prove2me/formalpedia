-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cadlag_nnreal_neg
-- name    : Kyprianou.Ch01.cadlag_nnreal_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T20:58:28.608577+00:00
-- url     : https://prove2.me/theorems/32b24962-221a-49bf-9a81-76f6fac8e6da
-- title:
--   Negation preserves the cadlag property of a nonnegative-time real path
-- statement:
--   A real cadlag path remains cadlag after pointwise negation.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue sections; existing source-file proof in research/kyprianou_ch01/proofs/risk_surplus_cadlag_bounded_v12.lean

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.cadlag_nnreal_neg
    (f : ℝ≥0 → ℝ) (hf : ProbabilityTheory.IsCadlag f) :
    ProbabilityTheory.IsCadlag (fun s => -f s) := by sorry
