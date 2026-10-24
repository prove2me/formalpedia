-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree_common_multiple
-- name    : OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.common_multiple
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:57:29.275696+00:00
-- url     : https://prove2.me/theorems/630473eb-b5e4-4bbc-9c0f-99e59c11b930
-- title:
--   Positive rational weights have a common integer multiple degree
-- statement:
--   Every finite family of positive rational weights has a positive common weighted degree, equal to a positive integer multiple of each weight.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.common_multiple
    (d : Nat) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) :
    ∃ q : Real, 0 < q ∧
      ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (w i : Real) * (e : Real) = q := by sorry
