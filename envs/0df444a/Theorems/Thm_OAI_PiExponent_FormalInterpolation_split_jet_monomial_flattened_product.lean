-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_split_jet_monomial_flattened_product
-- name    : OAI.PiExponent.FormalInterpolation.split_jet_monomial_flattened_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:28:07.763841+00:00
-- url     : https://prove2.me/theorems/50ad8291-bd97-4d3e-84e1-f0ce4709171a
-- title:
--   Split jet monomial as a flattened product
-- statement:
--   The split jet substitution sends a monomial to the flattening of the corresponding product with polynomial coefficients.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.split_jet_monomial_flattened_product
    {m : Nat} (j : Nat) (r : Fin m → Complex)
    (G : Fin m → Polynomial Complex)
    (e : Fin (m + 1) → Nat) :
    MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
        Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex)) =
    MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ)
      (MvPolynomial.C ((1 + Polynomial.X) ^ e 0) *
        ∏ i, (MvPolynomial.C (Polynomial.C ((j : Complex) * r i) + G i) +
          MvPolynomial.X i) ^ e i.succ) := by sorry
