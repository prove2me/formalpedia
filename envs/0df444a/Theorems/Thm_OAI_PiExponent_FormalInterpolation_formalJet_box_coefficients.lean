-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_box_coefficients
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_box_coefficients
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T17:10:30.512375+00:00
-- url     : https://prove2.me/theorems/877e9fd5-fde0-4071-bf2c-ae2b6977e30f
-- title:
--   Finite box approximation for the logarithmic formal jet
-- statement:
--   For every center parameter, finite box bound, and polynomial Q, there is a polynomial P whose image under the logarithmic formal substitution has the same coefficients as Q at every multivariate exponent whose coordinates are at most the bound.
-- source:
--   OpenAI Math, PiExponent/Jets/AlgebraicJetPackets.lean, triangularMap_comp_inverse and formalJet_packet_surjective; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.formalJet_box_coefficients
    {m : Nat} (c : Fin m -> Complex) (N : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      forall a : Fin (m + 1) -> Nat, (forall i, a i <= N) ->
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (FormalInterpolation.formalJet c P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (Q : MvPowerSeries (Fin (m + 1)) Complex) := by sorry
