-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree
-- name    : OAI.PiExponent.FormalInterpolation.exists_common_weight_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:41:41.754143+00:00
-- url     : https://prove2.me/theorems/a9add951-bbab-44dd-aaea-fdfff01b600c
-- title:
--   Choose a common weighted degree inside the strict rate gap
-- statement:
--   For finitely many positive rational weights and a strict gap between the representative rate and R, choose s at least N and a positive common weighted degree D strictly above s times the representative cutoff and strictly below sR, with D equal to each coordinate weight times a positive integer.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Rat.Cast.Defs

theorem OAI.PiExponent.FormalInterpolation.exists_common_weight_degree
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (R : Real) (hR : (rho : Real) < R)
    (eps : Real) (heps : 0 < eps)
    (C : Real) (hC : 0 ≤ C) (N : Nat)
    (hrate : (rho : Real) + eps < R) :
    ∃ s : Nat, 0 < s ∧ N ≤ s ∧
      ∃ D : Real, 0 < D ∧
        (s : Real) * ((rho : Real) + eps) + C < D ∧
        D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (w i : Real) * (e : Real) = D := by sorry
