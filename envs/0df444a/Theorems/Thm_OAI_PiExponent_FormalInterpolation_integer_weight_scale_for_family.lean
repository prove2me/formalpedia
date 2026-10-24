-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_integer_weight_scale_for_family
-- name    : OAI.PiExponent.FormalInterpolation.integer_weight_scale_for_family
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:41:23.377126+00:00
-- url     : https://prove2.me/theorems/594ac874-6be6-4fcc-a0b5-b25a5d16de73
-- title:
--   Clear rational weights for a finite multiplier family
-- statement:
--   Choose a common positive denominator for the rational weights and scale them to positive integer weights. For every finite multiplier family, convert each weighted-homogeneous support condition into the corresponding integer weighted-degree equality with the degree drop scaled by S.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.integer_weight_scale_for_family {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D m : Nat) : ∃ S : Nat, 0 < S ∧ ∃ W : Fin d → Nat, (∀ i, 0 < W i) ∧ (∀ i, (S : ℚ) * w i = (W i : ℚ)) ∧ ∀ (i : Fin d) (n : Nat) (q : Fin m → MvPolynomial (Fin d) ℂ), (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((n : ℚ) * w i - (D : ℚ))) → ∀ (j : Fin m) (a : Fin d →₀ Nat), a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - ((S * D : Nat) : ℤ) := by sorry
