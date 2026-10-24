-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_monomial_product_weight
-- name    : OAI.PiExponent.FormalInterpolation.support_monomial_product_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:02:58.172543+00:00
-- url     : https://prove2.me/theorems/a3d30cbf-ee29-4c0c-80d8-1a10a506df72
-- title:
--   Weight bound for a product of generator powers
-- statement:
--   If every supported exponent of each generator has weight at most `D`, every supported exponent of the product of generator powers has weight at most the total input exponent times `D`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.support_monomial_product_weight
    {d m : Nat} (w : Fin d → Rat) (D : Nat)
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ b ∈ (g j).support,
      ∑ k, (w k : Real) * (b k : Real) ≤ (D : Real))
    (u : Fin m →₀ Nat) (a : Fin d →₀ Nat)
    (ha : a ∈ (∏ j : Fin m, (g j) ^ (u j)).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤
      (∑ j, (u j : Real)) * (D : Real) := by sorry
