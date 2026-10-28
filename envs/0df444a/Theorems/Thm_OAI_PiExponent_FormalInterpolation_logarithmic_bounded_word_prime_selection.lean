-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_bounded_word_prime_selection
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_bounded_word_prime_selection
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:41:36.79421+00:00
-- url     : https://prove2.me/theorems/c116c9ad-0335-4a5c-99fe-cdc8eb2834c8
-- title:
--   Bounded-cost words admit a persistent minimal prime
-- statement:
--   Given the bounded-cost word hypotheses, construct a nonzero prime below Q that is minimal over a finite set of bounded-cost words applied to F, and is closed under every further word below the smaller cost cutoff. This isolates the component-selection argument; F is included among the generators.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_bounded_word_prime_selection
    {m : Nat} (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (m + 1)) Complex) (hF : F ≠ 0)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [Q.IsPrime]
    (hwords : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
        logarithmicFrameWord word F ∈ Q) :
    ∃ P : Ideal (MvPolynomial (Fin (m + 1)) Complex),
      P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ Q ∧
      ∃ S : Finset (MvPolynomial (Fin (m + 1)) Complex),
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P ∧
        F ∈ S ∧
        (∀ f ∈ S, ∃ word : List (Fin (m + 1)),
          f = logarithmicFrameWord word F ∧
          logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real)) ∧
        (∀ f ∈ S, ∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word <
            ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
          logarithmicFrameWord word f ∈ P) := by sorry
