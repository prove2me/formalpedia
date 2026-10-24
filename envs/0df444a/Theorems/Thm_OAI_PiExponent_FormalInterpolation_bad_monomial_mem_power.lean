-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bad_monomial_mem_power
-- name    : OAI.PiExponent.FormalInterpolation.bad_monomial_mem_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:17:21.209208+00:00
-- url     : https://prove2.me/theorems/b9978ab5-d653-4c1a-8d96-342b81b9e035
-- title:
--   An omitted evaluated monomial lies in the required ideal power
-- statement:
--   If every substituted generator lies in I^s and s times the exponent's total degree is at least n, then the evaluated monomial with any coefficient lies in I^n.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bad_monomial_mem_power
    {d m : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s n : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s) (u : Fin m →₀ Nat)
    (hu : n ≤ s * (∑ j : Fin m, u j)) (a : Complex) :
    MvPolynomial.aeval g (MvPolynomial.monomial u a) ∈ I ^ n := by sorry
