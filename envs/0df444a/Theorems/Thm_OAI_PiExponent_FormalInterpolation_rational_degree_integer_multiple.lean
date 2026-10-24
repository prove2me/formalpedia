-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_degree_integer_multiple
-- name    : OAI.PiExponent.FormalInterpolation.rational_degree_integer_multiple
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:08:36.625407+00:00
-- url     : https://prove2.me/theorems/5e01cb07-ccc2-4933-b0f5-833046878f91
-- title:
--   Clear a positive rational degree while preserving the strict slope bound
-- statement:
--   For a positive rational degree below the real threshold `sR`, choose a positive integer multiple `D` of that degree that remains strictly below the correspondingly scaled threshold. This supplies the integer degree and slope bound used by the parent.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

theorem OAI.PiExponent.FormalInterpolation.rational_degree_integer_multiple
    (s : Nat) (q : Rat) (R : Real) (B : Nat)
    (hs : 0 < s) (hB : (B : Real) < (s : Real) * R)
    (hq : 0 < q) (hqB : (q : Real) ≤ (B : Real)) :
    ∃ m D : Nat, 0 < m ∧ 0 < D ∧
      q * (m : Rat) = (D : Rat) ∧
      (D : Real) < ((s * m : Nat) : Real) * R := by sorry
