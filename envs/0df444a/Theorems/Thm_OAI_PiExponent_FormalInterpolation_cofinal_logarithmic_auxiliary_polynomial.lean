-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_cofinal_logarithmic_auxiliary_polynomial
-- name    : OAI.PiExponent.FormalInterpolation.cofinal_logarithmic_auxiliary_polynomial
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T03:41:36.244987+00:00
-- url     : https://prove2.me/theorems/37b32db9-b4fa-4962-a716-06d294426f6e
-- title:
--   Cofinal auxiliary polynomials with weighted logarithmic jet vanishing
-- statement:
--   The strict full-dimensional volume inequality supplies nonzero polynomials of arbitrarily large natural height N, with w-weight at most N and every logarithmic jet vanishing at all v-weights strictly below (1+3 sigma)N.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.cofinal_logarithmic_auxiliary_polynomial
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hvolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
        (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1) :
    ∀ N₀ : Nat, ∃ N : Nat, N₀ ≤ N ∧ 0 < N ∧
      ∃ F : MvPolynomial (Fin (m + 1)) Complex, F ≠ 0 ∧
        logarithmicDegreeBound w (N : Real) F ∧
        logarithmicJetBound c v ((1 + 3 * (sigma : Real)) * (N : Real)) F := by sorry
