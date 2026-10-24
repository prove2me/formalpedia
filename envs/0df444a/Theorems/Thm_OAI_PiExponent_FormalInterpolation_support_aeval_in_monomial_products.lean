-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_aeval_in_monomial_products
-- name    : OAI.PiExponent.FormalInterpolation.support_aeval_in_monomial_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:02:47.909556+00:00
-- url     : https://prove2.me/theorems/dab1b713-f8e6-4739-ad5f-fd86d8d54a73
-- title:
--   Support of evaluated polynomial comes from an input monomial
-- statement:
--   Every exponent in the support of an evaluated polynomial belongs to the support of the evaluated monomial product for some exponent in the original polynomial's support.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.support_aeval_in_monomial_products
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (f : MvPolynomial (Fin m) Complex) (a : Fin d →₀ Nat)
    (ha : a ∈ (MvPolynomial.aeval g f).support) :
    ∃ u ∈ f.support, a ∈ (∏ j : Fin m, (g j) ^ (u j)).support := by sorry
