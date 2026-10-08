-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_formalJet_polynomial_approximation
-- name    : OAI.PiExponent.FormalInterpolation.finite_formalJet_polynomial_approximation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:29:41.63768+00:00
-- url     : https://prove2.me/theorems/b97b0872-ab33-4165-a625-75a778f23fe1
-- title:
--   Finite polynomial approximation under logarithmic substitution
-- statement:
--   Given any finite set of multivariate formal-series coefficients and any ordinary polynomial Q in the series coordinates, there is a polynomial P in the original variables whose image under the logarithmic substitution has the same selected coefficients as Q. Truncating the inverse logarithmic coordinate change to sufficiently high finite order yields a polynomial preimage with the prescribed finite jet.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean, triangularMap_comp_inverse and formalJet_packet_surjective

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.finite_formalJet_polynomial_approximation
    {m : ℕ} (c : Fin m → ℂ) (S : Finset (Fin (m + 1) → ℕ))
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : ↥ S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet c P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (Q : MvPowerSeries (Fin (m + 1)) ℂ) := by sorry
