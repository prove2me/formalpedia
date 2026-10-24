-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_weights_common_degree_rounding
-- name    : OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_rounding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:39:33.207441+00:00
-- url     : https://prove2.me/theorems/991f713c-0cbe-4217-9fc2-6b0b1f1442f6
-- title:
--   Common-degree rounding with bounded overhead
-- statement:
--   For a finite family of positive rational weights sharing the integer scale L, round all positive exponents up to one common weighted degree, with multiplier q at least Q and degree at most qB+L. The common-multiple and finite-ceiling construction also covers the empty family, where the coordinate requirements are vacuous.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

theorem OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_rounding
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i : Fin d, 0 < (w i : Real))
    (B : Nat) (L : Nat) (hL : 0 < L) (c : Fin d → Nat)
    (hc : ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real))
    (n : Fin d → Nat)
    (hn : ∀ i : Fin d, 0 < n i ∧ (n i : Real) * (w i : Real) ≤ (B : Real))
    (Q : Nat) :
    ∃ q : Nat, ∃ D : Nat, 0 < q ∧ Q ≤ q ∧ 0 < D ∧
      (D : Real) ≤ ((q * B + L : Nat) : Real) ∧
      ∀ i : Fin d, ∃ m : Nat,
        q * n i ≤ m ∧ 0 < m ∧ (m : Real) * (w i : Real) = (D : Real) := by sorry
