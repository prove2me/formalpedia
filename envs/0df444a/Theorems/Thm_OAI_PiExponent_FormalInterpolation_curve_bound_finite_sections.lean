-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_finite_sections
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_finite_sections
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T19:26:23.191318+00:00
-- url     : https://prove2.me/theorems/a597fb9c-3d4c-429a-a012-3a90dc8e232f
-- title:
--   Curve bound yields a finite family of bounded sections
-- statement:
--   From the curve bound and finite colength, find one ordinary power I^s and a finite family of sections inside it whose span contains a positive power of every coordinate, retaining the strict weighted slope bound.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_finite_sections
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ (s : Nat) (S : Finset (MvPolynomial (Fin d) Complex)),
      0 < s ∧
      (∀ f ∈ S, f ∈ I ^ s) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by sorry
