-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_coordinate_ratio
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_coordinate_ratio
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:57:16.791761+00:00
-- url     : https://prove2.me/theorems/bd7eff29-7df0-4802-b31c-1597a1a53750
-- title:
--   Coordinate ratio for canonical logarithmic interpolation weights
-- statement:
--   At every successor coordinate, `(1 + sigma) * w` is strictly less than `v`. The intended route is the strict scale inequality `sigma_theta` combined with positivity of the canonical logarithmic weight.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_coordinate_ratio {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ i : Fin d.m, (1 + (d.sigma : Real)) * (w i.succ : Real) < (v i.succ : Real)) := by sorry
