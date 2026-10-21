-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_full_product_ratio
-- name    : OAI.PiExponent.FormalInterpolation.canonical_full_product_ratio
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:44:43.30195+00:00
-- url     : https://prove2.me/theorems/67ab1006-6f57-49c8-a78a-1628cdc84dd6
-- title:
--   Full canonical logarithmic product ratio
-- statement:
--   The ratio of the full canonical weight product to the full canonical jet product equals the distinguished-coordinate ratio multiplied by theta to the power m. The index-zero factor contributes w0/v0; each successor coordinate contributes theta after cancellation. This is the product identity needed to apply `sigma_volume`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.canonical_full_product_ratio {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (∏ i, (w i : Real)) / (∏ i, (v i : Real)) =
       ((d.w0 : Real) / (d.v0 : Real)) * (d.base.theta : Real) ^ d.m) := by sorry
