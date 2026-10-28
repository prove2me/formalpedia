-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinatewise_curve_bounded_sections
-- name    : OAI.PiExponent.FormalInterpolation.coordinatewise_curve_bounded_sections
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T19:30:25.403324+00:00
-- url     : https://prove2.me/theorems/bf553de9-8b44-49c0-855d-f1e91807cfd1
-- title:
--   Curve bound gives coordinatewise bounded ordinary-power sections
-- statement:
--   For each coordinate separately, produce a positive ordinary power of the ideal and a finite family inside that power whose span contains a positive coordinate power with strict weighted slope below rho plus eps.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinatewise_curve_bounded_sections
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∀ i : Fin d, ∃ s : Nat, ∃ n : Nat,
      ∃ F : Finset (MvPolynomial (Fin d) Complex),
        0 < s ∧ 0 < n ∧
        (∀ f ∈ F, f ∈ I ^ s) ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (F : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by
  sorry
