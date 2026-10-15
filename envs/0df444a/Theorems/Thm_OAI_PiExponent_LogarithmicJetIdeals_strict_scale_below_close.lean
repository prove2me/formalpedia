-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_scale_below_close
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_scale_below_close
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T19:07:01.280681+00:00
-- url     : https://prove2.me/theorems/32ba7e60-db05-47cb-9fdf-c9cba26f308f
-- title:
--   A strict lower scale can retain the power inequality
-- statement:
--   For every positive exponent and positive scale, there is a positive strictly smaller scale whose nth power is more than half the original nth power. For example, take `R = S * (1 - 1 / (4*n))` and apply Bernoulli's inequality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_scale_below_close
    (n : ℕ) (hn : 0 < n) (S : ℝ) (hS : 0 < S) :
    ∃ R : ℝ, 0 < R ∧ R < S ∧ 2 * R ^ n > S ^ n := by sorry
