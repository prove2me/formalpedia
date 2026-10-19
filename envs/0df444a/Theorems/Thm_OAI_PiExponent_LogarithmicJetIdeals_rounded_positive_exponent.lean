-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rounded_positive_exponent
-- name    : OAI.PiExponent.LogarithmicJetIdeals.rounded_positive_exponent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T23:03:31.949996+00:00
-- url     : https://prove2.me/theorems/7bd12c19-3563-48bf-ba5f-a9d52e9fd4eb
-- title:
--   Round a positive weight past a cutoff
-- statement:
--   For each positive variable weight, choose the least natural exponent whose weighted degree strictly exceeds the nonnegative cutoff. It is positive and exceeds the cutoff by at most one weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.rounded_positive_exponent (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (D : ℝ) (hD : 0 ≤ D) : ∀ i, ∃ N : ℕ, 0 < N ∧ D < (N : ℝ) * w i ∧ (N : ℝ) * w i ≤ D + w i := by sorry
