-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_separation
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_separation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:56:58.029799+00:00
-- url     : https://prove2.me/theorems/c08346c2-c343-407d-98ec-2c9785a61230
-- title:
--   Separation inequality for canonical logarithmic weights
-- statement:
--   For equally sized index sets that differ at a nonzero index and agree above it, the canonical weights satisfy the required strict separation product inequality. This isolates the use of `weight_growth` and its separation factor, including the strict membership and ordering conditions of the numerical field.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_separation {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ A B : Finset (Fin (d.m + 1)), A.card = B.card →
       ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
         (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
           interpolationSeparationConstant d.m d.sigma * (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real)) := by sorry
