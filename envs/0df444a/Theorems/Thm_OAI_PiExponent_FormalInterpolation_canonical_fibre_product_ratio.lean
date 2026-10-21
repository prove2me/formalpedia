-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_fibre_product_ratio
-- name    : OAI.PiExponent.FormalInterpolation.canonical_fibre_product_ratio
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:45:03.850723+00:00
-- url     : https://prove2.me/theorems/ab27db80-865d-40f3-97c6-8959936e4dea
-- title:
--   Successor-coordinate canonical product ratio
-- statement:
--   The ratio over successor coordinates alone equals theta to the power m. The distinguished index-zero weights are excluded, matching the fibre product in `sigma_centers`. This identity handles the second strict inequality independently of the full-product calculation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.canonical_fibre_product_ratio {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (∏ i : Fin d.m, (w i.succ : Real)) / (∏ i : Fin d.m, (v i.succ : Real)) =
       (d.base.theta : Real) ^ d.m) := by sorry
