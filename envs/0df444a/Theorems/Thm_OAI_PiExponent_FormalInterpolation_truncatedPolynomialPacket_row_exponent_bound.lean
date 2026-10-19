-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_row_exponent_bound
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_row_exponent_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:11:59.195018+00:00
-- url     : https://prove2.me/theorems/231fabad-91e4-4489-9137-0981e08f409d
-- title:
--   Strict row exponents lie in the prescribed box
-- statement:
--   Each exponent vector in a strict weighted row belongs to the coordinate box whose side lengths are `n * e i`. Positivity follows from `R = e i * rowWeight i`, `R > 0`, and `e i > 0`; the strict weighted sum then bounds each individual coordinate. This also rules out rows when `n = 0`. It supplies the support inclusion needed to apply finite-box realization and gluing.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_row_exponent_bound
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (n : Nat)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : Real) * R))
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i) :
    ∀ i, rho.2.1 i < n * e i := by sorry
