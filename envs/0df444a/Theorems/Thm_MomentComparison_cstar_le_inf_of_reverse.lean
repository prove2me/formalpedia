-- Prove2me | Theorems.Thm_MomentComparison_cstar_le_inf_of_reverse
-- name    : MomentComparison.cstar_le_inf_of_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:03:54.26674+00:00
-- url     : https://prove2.me/theorems/17831997-3ef8-4bf9-b497-ac22c625b262
-- title:
--   Moment Comparison: cstar le inf of reverse
-- statement:
--   Reduces the upper bound to a uniform reverse comparison for conjugate exponents.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L127-L140
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L127-L140

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.cstar_le_inf_of_reverse {L : ℝ → ℝ}
    (hL : ∀ p, 2 < p → 0 < L p)
    (hReverse : ∀ p, 2 < p → ∀ {n d : ℕ} (f : Cube n → ℝ), HasDegreeLE f d →
      complexMomentNorm p (fun x => (f x : ℂ)) ≤
        L p ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Cstar ≤ sInf ((fun p => L p ^ (p / (2 * (p - 2)))) '' Set.Ioi 2) := by sorry
