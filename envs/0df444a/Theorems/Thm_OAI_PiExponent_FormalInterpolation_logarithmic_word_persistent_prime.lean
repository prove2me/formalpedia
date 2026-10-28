-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_word_persistent_prime
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_word_persistent_prime
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T23:14:18.054619+00:00
-- url     : https://prove2.me/theorems/4b5b9633-39f3-4a4d-96cd-1fcbf52bb889
-- title:
--   A bounded-cost derivative filtration has a persistent prime component
-- statement:
--   Construct the m+3 derivative-ideal levels with spacing delta = sigma N/(m+2). Positive costs make their generating word sets finite. Choose minimal primes backwards inside Q; the polynomial-ring dimension bound forces two adjacent primes to coincide. Their equality gives persistence for every further word of cost strictly below delta. The empty word puts the nonzero F in P, ensuring P is nonzero. Frame words preserve the weighted degree bound because all degree weights are positive. This isolates the component-selection argument without separation, contact, or curve hypotheses.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_word_persistent_prime
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (m + 1)) Complex) (hF : F ≠ 0)
    (hdegree : logarithmicDegreeBound w (N : Real) F)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [Q.IsPrime]
    (hwords : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
        logarithmicFrameWord word F ∈ Q) :
    ∃ P : Ideal (MvPolynomial (Fin (m + 1)) Complex),
      P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ Q ∧
      ∃ S : Finset (MvPolynomial (Fin (m + 1)) Complex),
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P ∧
        (∀ f ∈ S, logarithmicDegreeBound w (N : Real) f) ∧
        (∀ f ∈ S, ∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word <
            ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
          logarithmicFrameWord word f ∈ P) := by sorry
