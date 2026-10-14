-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_truncated_polynomial_jets_surjective
-- name    : OAI.PiExponent.FormalInterpolation.finite_truncated_polynomial_jets_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:04:57.833966+00:00
-- url     : https://prove2.me/theorems/b15cec34-dbd8-4774-b9e2-827c98fd6e62
-- title:
--   Finite truncated polynomial jets interpolate independently at distinct centers
-- statement:
--   At distinct centers jr, an unrestricted polynomial can realize any prescribed finite packet of coefficients after the truncated logarithmic polynomial substitution.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_truncated_polynomial_jets_surjective
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hcenters : Function.Injective
      (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i)) :
    Function.Surjective (truncatedPolynomialPacket K v0 theta w H r T) := by sorry
