-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion
-- name    : OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T05:55:14.658137+00:00
-- url     : https://prove2.me/theorems/fa041992-641e-43bb-b856-2369dad905f9
-- title:
--   Expand a truncated polynomial jet coefficient over support
-- statement:
--   For a polynomial evaluated by the truncated polynomial jet, the coefficient at exponent vector `a` is the sum over the polynomial's support. Each summand is its coefficient multiplied by the corresponding interpolation entry, with row scale `j` and exponents taken from `a`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T P).coeff
        (InterpolationMatrix.exponentVector a) =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          j (a 0) (fun i => a i.succ) (e 0) (fun i => e i.succ) := by sorry
