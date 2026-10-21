-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_volume_bounds
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_volume_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:56:42.71699+00:00
-- url     : https://prove2.me/theorems/6b5f955a-5c4e-457c-b3b8-8e2e5585ec2f
-- title:
--   Volume bounds for canonical logarithmic interpolation weights
-- statement:
--   The canonical weights satisfy the full and successor-coordinate volume bounds required by `LogarithmicInterpolationNumerics`. These are the parameter-margin estimates to prove from `volume_eq`, `volume_lt_one`, `sigma_volume`, and `sigma_centers`, preserving the distinct full and fibre products.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_volume_bounds {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (d.K : Real) * (1 + 3 * (d.sigma : Real)) ^ (d.m + 1) * (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1) ∧
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (d.K : Real) * (1 + 3 * (d.sigma : Real)) ^ d.m * (∏ i : Fin d.m, (w i.succ : Real)) / (∏ i : Fin d.m, (v i.succ : Real)) < 1) := by sorry
