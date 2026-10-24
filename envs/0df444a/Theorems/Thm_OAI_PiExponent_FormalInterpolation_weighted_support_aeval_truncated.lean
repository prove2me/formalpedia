-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_aeval_truncated
-- name    : OAI.PiExponent.FormalInterpolation.weighted_support_aeval_truncated
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:52:58.613873+00:00
-- url     : https://prove2.me/theorems/b35d7a67-8cbc-4ab1-9711-25273b4758e2
-- title:
--   Weighted support bound for truncated evaluation
-- statement:
--   A strict total-degree cutoff on a polynomial’s support, together with a uniform weighted bound on the evaluated generators, bounds every support weight after evaluation. The key proof work is the monomial expansion and the strict real inequality; the cutoff remains strict, including at the zero-degree boundary.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_support_aeval_truncated
    {d m : Nat} (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (f : MvPolynomial (Fin m) Complex) (n : Nat)
    (hcut : ∀ u ∈ f.support, s * (∑ j, u j) < n) :
    ∀ a ∈ (MvPolynomial.aeval g f).support,
      ∑ k, (w k : Real) * (a k : Real) ≤
        (n : Real) * ((rho : Real) + eps) := by sorry
