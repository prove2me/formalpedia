-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_subcritical_quotient_representatives
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_subcritical_quotient_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T12:33:37.118644+00:00
-- url     : https://prove2.me/theorems/7f34f78d-e38b-4906-9997-36e0ace29d80
-- title:
--   Subcritical representatives for logarithmic center ideal powers
-- statement:
--   There is a fixed positive rational rate δ strictly below R such that, for all sufficiently large powers n of the canonical logarithmic centers ideal, every polynomial has a representative modulo that power whose support has weighted degree at most nδ.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_subcritical_quotient_representatives
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ δ : Rat, 0 < δ ∧ δ < R ∧ ∃ n₀ : Nat,
      ∀ n : Nat, n₀ ≤ n → ∀ p : MvPolynomial (Fin (m + 1)) Complex,
        ∃ q : MvPolynomial (Fin (m + 1)) Complex,
          p - q ∈ logarithmicCentersIdeal c (fun _ => e 0) e ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * (δ : Real) := by sorry
