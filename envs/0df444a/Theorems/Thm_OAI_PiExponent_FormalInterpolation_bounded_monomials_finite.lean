-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_monomials_finite
-- name    : OAI.PiExponent.FormalInterpolation.bounded_monomials_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:35:39.718997+00:00
-- url     : https://prove2.me/theorems/7eefa5ad-f536-40bb-8b28-e3ae6340837c
-- title:
--   Finiteness of coordinate-bounded monomials
-- statement:
--   For a finite set of variables, the monomials whose exponent in each coordinate is below a fixed natural bound form a finite set.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_monomials_finite {d : Nat} (n : Fin d → Nat) : ({f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)}).Finite := by sorry
