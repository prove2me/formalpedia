-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T08:26:36.940202+00:00
-- url     : https://prove2.me/theorems/4a88b1cc-6119-4de3-a430-313b0c53cb51
-- title:
--   Critical weighted representatives from logarithmic interpolation numerics
-- statement:
--   Positive rational degree and jet weights satisfying the logarithmic curve-contact numerical criteria give eventual representatives of weight at most nR modulo the nth ordinary power of the canonical product ideal, for centers injective in every coordinate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
          P - Q ∈ (logarithmicCentersIdeal c (fun _ => e 0) e) ^ n ∧
          ∀ a ∈ Q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * (R : Real) := by sorry
