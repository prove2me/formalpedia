-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_polynomial_representations
-- name    : OAI.PiExponent.FormalInterpolation.truncate_polynomial_representations
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T08:44:03.992982+00:00
-- url     : https://prove2.me/theorems/553da36d-d6fd-4f23-934e-09271b0a961a
-- title:
--   Truncating generator expressions gives bounded quotient representatives
-- statement:
--   Given polynomial-module representations in the generators, truncate every outer polynomial expression at generator-product length below the ideal-power cutoff. The discarded terms vanish modulo `I^n`; the retained terms satisfy the required weighted-degree rate, up to a constant from the fixed module generators.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncate_polynomial_representations
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hrepr : ∀ q : MvPolynomial (Fin d) Complex,
      ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
        ∃ F : Fin t → MvPolynomial (Fin m) Complex,
          q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i) :
    ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C := by sorry
