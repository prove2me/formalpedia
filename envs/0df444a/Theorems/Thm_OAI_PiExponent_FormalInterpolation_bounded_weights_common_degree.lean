-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_weights_common_degree
-- name    : OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:29:55.72282+00:00
-- url     : https://prove2.me/theorems/50b48f9f-3b6b-4157-9565-1f50b122a784
-- title:
--   Bounded coordinate weights extend to one common degree
-- statement:
--   Given positive rational weights with a common integer scale, positive coordinate exponents whose weighted degrees are bounded by `B`, and the strict cutoff `B < s * R`, choose one positive multiplier and one positive common weighted degree below the scaled cutoff, with a scaled exponent at least `q * n i` for every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

theorem OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i : Fin d, 0 < (w i : Real))
    (R : Real) (s : Nat) (hs : 0 < s) (B : Nat)
    (hBR : (B : Real) < (s : Real) * R)
    (L : Nat) (hL : 0 < L) (c : Fin d → Nat)
    (hc : ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real))
    (n : Fin d → Nat)
    (hn : ∀ i : Fin d, 0 < n i ∧ (n i : Real) * (w i : Real) ≤ (B : Real)) :
    ∃ q : Nat, ∃ D : Nat, 0 < q ∧ 0 < D ∧
      (D : Real) < ((s * q : Nat) : Real) * R ∧
      ∀ i : Fin d, ∃ m : Nat,
        q * n i ≤ m ∧ 0 < m ∧ (m : Real) * (w i : Real) = (D : Real) := by sorry
