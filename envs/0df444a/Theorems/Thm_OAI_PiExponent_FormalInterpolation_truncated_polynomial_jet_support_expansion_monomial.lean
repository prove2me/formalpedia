-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion_monomial
-- name    : OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:59:00.719278+00:00
-- url     : https://prove2.me/theorems/2021d5d3-97cb-42bc-9e22-3f07efcf3acd
-- title:
--   Identify a jet monomial coefficient with an interpolation entry
-- statement:
--   For a monomial with exponent function `e`, the coefficient of its image under the truncated polynomial jet equals the interpolation entry indexed by the corresponding exponents of `e` and the requested coefficient index `a`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_monomial
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (e a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector a) =
      InterpolationMatrix.entry
        r (fun i => InterpolationMatrix.truncatedLog (T i))
        j (a 0) (fun i => a i.succ) (e 0) (fun i => e i.succ) := by sorry
