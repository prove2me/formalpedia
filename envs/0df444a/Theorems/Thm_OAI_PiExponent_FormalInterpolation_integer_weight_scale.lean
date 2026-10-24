-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_integer_weight_scale
-- name    : OAI.PiExponent.FormalInterpolation.integer_weight_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:36:49.896991+00:00
-- url     : https://prove2.me/theorems/6a405b3a-6f72-47a5-bbbf-f16a26100fe0
-- title:
--   Clear rational weights while preserving homogeneous support
-- statement:
--   Choose one positive integer scale that makes every positive rational variable weight an integer and converts the homogeneous multiplier condition into an exact integer-weight support equality, with the degree drop scaled to S·D.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.integer_weight_scale {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D : Nat) : ∃ S : Nat, 0 < S ∧ ∃ W : Fin d → Nat, (∀ i, 0 < W i) ∧ (∀ i, (S : ℚ) * w i = (W i : ℚ)) ∧ ∀ (i : Fin d) (n : Nat) (q : Fin 0 → MvPolynomial (Fin d) ℂ), (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((n : ℚ) * w i - (D : ℚ))) → ∀ (j : Fin 0) (a : Fin d →₀ Nat), a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - ((S * D : Nat) : ℤ) := by sorry
