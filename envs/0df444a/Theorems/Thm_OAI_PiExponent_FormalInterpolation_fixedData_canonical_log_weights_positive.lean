-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_weights_positive
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:56:30.279203+00:00
-- url     : https://prove2.me/theorems/1e065f7d-c60b-4baf-94e5-563722a314e7
-- title:
--   Positivity of canonical logarithmic interpolation weights
-- statement:
--   The canonical rational column and row weights are positive, and the number of nonzero coordinates is positive. This supplies the positivity fields of the numerical structure; prove the successor-coordinate claims from `x_one_le` and the base-coordinate claims from the positivity hypotheses on the fixed data.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    1 ≤ d.m ∧
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     ∀ i, 0 < (w i : Real)) ∧
    (let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ i, 0 < (v i : Real)) := by sorry
