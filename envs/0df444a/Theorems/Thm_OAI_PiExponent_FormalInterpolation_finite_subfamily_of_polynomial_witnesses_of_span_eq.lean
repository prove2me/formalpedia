-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_subfamily_of_polynomial_witnesses_of_span_eq
-- name    : OAI.PiExponent.FormalInterpolation.finite_subfamily_of_polynomial_witnesses_of_span_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:40:48.347142+00:00
-- url     : https://prove2.me/theorems/d5080f12-77dd-48f7-b159-4befe8cdd994
-- title:
--   Equal generated ideals preserve the common-zero implication
-- statement:
--   If a finite indexed subfamily generates the same ideal as the full polynomial family, then any common zero of that subfamily is a common zero of the full family and therefore has all coordinates zero under the parent hypothesis.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Polynomial.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_subfamily_of_polynomial_witnesses_of_span_eq
    {d : Nat} {α : Type}
    (F : α → MvPolynomial (Fin d) Complex)
    (m : Nat) (idx : Fin m → α)
    (hspan :
      Ideal.span (Set.range (fun j : Fin m => F (idx j))) =
        Ideal.span (Set.range F))
    (h : ∀ x : Fin d → Complex,
      (∀ a : α, MvPolynomial.eval x (F a) = 0) →
      ∀ i : Fin d, x i = 0) :
    ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (F (idx j)) = 0) →
      ∀ i : Fin d, x i = 0 := by sorry
