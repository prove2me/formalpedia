-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_degree_of_truncated_generator_sum
-- name    : OAI.PiExponent.FormalInterpolation.weighted_degree_of_truncated_generator_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:08:09.823982+00:00
-- url     : https://prove2.me/theorems/cb7eb954-80b3-4ee5-8546-3a8479298ea0
-- title:
--   Bound the support weights of a truncated generator sum
-- statement:
--   Every support monomial in the assembled truncated sum has weight at most n · (rho + eps) + C. Prove this by bounding each evaluated generator monomial using hdeg, applying the strict cutoff and hD, adding the bound hb for b_i, and observing that support weights of a sum are bounded by the maximum of the summand bounds.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_degree_of_truncated_generator_sum
    {d m t : Nat} (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (b : Fin t → MvPolynomial (Fin d) Complex)
    (C : Real) (hb : ∀ i, ∀ a ∈ (b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ C)
    (n : Nat) (F G : Fin t → MvPolynomial (Fin m) Complex)
    (hG : ∀ i, ∀ u ∈ (G i).support, s * (∑ j, u j) < n) :
    ∀ a ∈ (∑ i : Fin t, MvPolynomial.aeval g (G i) * b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤
        (n : Real) * ((rho : Real) + eps) + C := by sorry
