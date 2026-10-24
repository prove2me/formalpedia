-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_initial_ideal_pointwise
-- name    : OAI.PiExponent.FormalInterpolation.bounded_initial_ideal_pointwise
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:39:46.976031+00:00
-- url     : https://prove2.me/theorems/3111476c-a62e-4d35-a5fd-87d6a57fe281
-- title:
--   Coordinate powers yield pointwise bounded sections
-- statement:
--   From a positive power of each coordinate in the stated ideal span, any point with a nonzero coordinate yields a bounded element of `I ^ s` whose degree-`D` component evaluates nonzero. Evaluate the coordinate-power relation at that point: since the power has nonzero evaluation, its finite ideal-span expression must contain a generator whose initial component has nonzero evaluation. The generator supplies the required support bound and membership. For `d = 0`, the pointwise premise has no witnesses. This is an algebraic extraction step independent of the curve criterion.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_initial_ideal_pointwise
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hs : 0 < s) (hD : 0 < D)
    (hcoords : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
        ∃ g : MvPolynomial (Fin d) Complex,
          g ∈ I ^ s ∧
          (∀ a ∈ g.support,
            ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
          h = MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g}) :
    ∀ x : Fin d → Complex,
      (∃ i : Fin d, x i ≠ 0) →
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ s ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0 := by sorry
