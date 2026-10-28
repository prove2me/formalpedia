-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_ideal_finite_colength_coordinate_powers_20261024
-- name    : OAI.PiExponent.FormalInterpolation.homogeneous_ideal_finite_colength_coordinate_powers_20261024
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T15:08:02.996144+00:00
-- url     : https://prove2.me/theorems/3cc82a89-089b-44f8-8661-c3726dd6df3b
-- title:
--   Finite colength of a homogeneous ideal forces coordinate powers
-- statement:
--   If S consists of weighted degree-q components and the quotient by its span is finite-dimensional, then every coordinate has a positive power in the span. This isolates the graded-algebra step from the geometric child. A proof route uses the induced positive weighted grading: distinct powers of each coordinate have distinct degrees, while finite-dimensionality prevents infinitely many independent degree classes. Positive weights ensure this degree separation; q > 0 is retained as in the parent interface. For d = 0 the conclusion is vacuous.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.homogeneous_ideal_finite_colength_coordinate_powers_20261024
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (q : Rat) (hq : 0 < q) (S : Set (MvPolynomial (Fin d) Complex))
    (hhom : ∀ p ∈ S, ∃ g,
      p = MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q g)
    (hfinite : Module.Finite Complex
      (MvPolynomial (Fin d) Complex ⧸ Ideal.span S)) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span S := by sorry
