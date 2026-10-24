-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_isWeightedHomogeneous_X_pow
-- name    : OAI.PiExponent.FormalInterpolation.isWeightedHomogeneous_X_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:13:35.25444+00:00
-- url     : https://prove2.me/theorems/40fad82a-dc28-4f07-9d5b-7ba346bacf62
-- title:
--   Variable powers have their expected weighted degree
-- statement:
--   A power of one variable is weighted homogeneous, with degree equal to the exponent times that variable's weight. The explicit polynomial type fixes the coefficient ring, and the statement includes exponent zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.isWeightedHomogeneous_X_pow
    {d : Nat} (w : Fin d → Rat) (i : Fin d) (e : Nat) :
    MvPolynomial.IsWeightedHomogeneous (fun i => (w i : Real))
      ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e)
      ((e : Real) * (w i : Real)) := by sorry
