-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T08:48:49.849258+00:00
-- url     : https://prove2.me/theorems/1edb2b1b-b227-4dd3-aedb-e225a764ca45
-- title:
--   Eventual strict-margin representatives from logarithmic interpolation numerics
-- statement:
--   Under the logarithmic interpolation numerical hypotheses and coordinatewise injectivity of the centers, there is a fixed strict margin below R such that every polynomial, for all sufficiently large powers n, has a representative modulo the nth power of the canonical logarithmic product ideal with support weight at most n times that margin.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ δ : Real, 0 < δ ∧ δ < (R : Real) ∧
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ∀ P : MvPolynomial (Fin (m + 1)) Complex,
          ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
            P - Q ∈ (logarithmicCentersIdeal c (fun _ => e 0) e) ^ n ∧
            ∀ a ∈ Q.support,
              ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * δ := by sorry
