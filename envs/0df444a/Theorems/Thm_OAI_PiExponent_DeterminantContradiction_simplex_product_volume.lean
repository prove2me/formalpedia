-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_product_volume
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_product_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:08:06.899274+00:00
-- url     : https://prove2.me/theorems/a6044a1d-19f3-48e9-9add-024cde1ea36c
-- title:
--   Volume of the joint standard simplex
-- statement:
--   The Lebesgue volume of the nonnegative `(n+1)`-coordinate simplex with coordinate sum below T is `T^(n+1)/(n+1)!`.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_product_volume (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume {z : Real × (Fin n → Real) | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T} = ENNReal.ofReal (T ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
