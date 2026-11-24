-- Prove2me | Theorems.Thm_MomentComparison_realMomentNorm_le_of_pairing
-- name    : MomentComparison.realMomentNorm_le_of_pairing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:04:18.063746+00:00
-- url     : https://prove2.me/theorems/a61fa445-e6d2-4c7d-91ed-a4f6e8908b11
-- title:
--   Moment Comparison: real Moment Norm le of pairing
-- statement:
--   A bound on every scalar pairing implies the corresponding moment norm bound.
--   For real functions the dual witness is `x ↦ f x * |f x|^(p - 2)`.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L144-L190
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L144-L190

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

theorem MomentComparison.realMomentNorm_le_of_pairing {n : ℕ} {p q M : ℝ} (hp : 2 < p)
    (hpq : p.HolderConjugate q) (hM : 0 ≤ M) (f : Cube n → ℝ)
    (hbound : ∀ g : Cube n → ℂ,
      ‖(∑ x, (f x : ℂ) * g x) / (2 : ℂ) ^ n‖ ≤ M * complexMomentNorm q g) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤ M := by sorry
