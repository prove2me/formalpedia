-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_integral_coordinates_over_repair6
-- name    : OAI.PiExponent.FormalInterpolation.finite_of_integral_coordinates_over_repair6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:20:38.635955+00:00
-- url     : https://prove2.me/theorems/f9f37ecc-e188-42ff-bd1e-d60e1e03b7c2
-- title:
--   Integral coordinates imply module finiteness
-- statement:
--   Given integrality of every coordinate over A, prove the polynomial ring is finite as an A-module. A monic equation for each coordinate bounds its powers, and products of those bounded powers span the ring. For d = 0, the coordinate premise is vacuous. This removes the finite-module step from the parent; the remaining work is to formalize the finite spanning family from the monic equations.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_of_integral_coordinates_over_repair6
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by sorry
