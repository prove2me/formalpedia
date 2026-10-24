-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_weights_common_integer_scale
-- name    : OAI.PiExponent.FormalInterpolation.rational_weights_common_integer_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:29:29.890569+00:00
-- url     : https://prove2.me/theorems/d84e1672-c570-42ce-b902-a99ddab7eda8
-- title:
--   Positive rational weights admit a common integer scale
-- statement:
--   For a finite family of positive rational weights, choose one positive natural number that is an integer multiple of every weight, witnessed by positive natural multipliers.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

theorem OAI.PiExponent.FormalInterpolation.rational_weights_common_integer_scale
    {d : Nat} (w : Fin d → Rat)
    (hw : ∀ i : Fin d, 0 < (w i : Real)) :
    ∃ L : Nat, 0 < L ∧ ∃ c : Fin d → Nat,
      ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real) := by sorry
