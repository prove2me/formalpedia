-- Prove2me | Theorems.Thm_MomentComparison_twoPoint_contract
-- name    : MomentComparison.twoPoint_contract
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:52:42.042162+00:00
-- url     : https://prove2.me/theorems/bb8c369a-35e6-4859-a5a4-8891335d0882
-- title:
--   Moment Comparison: two Point contract
-- statement:
--   Complex noise is contractive from the conjugate moment to the `p` moment
--   for a two-point cube when the noise parameter lies in the lens.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPointReduction.lean#L98-L101
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPointReduction.lean#L98-L101

module
public import Definitions.Def_MomentComparison_TwoPoint
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_TwoPointReduction
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.twoPoint_contract {p : ℝ} (hp : 2 < p) {w : ℂ} (hw : inLens p w) (a b : ℂ) :
    ((‖a + w * b‖ ^ p + ‖a - w * b‖ ^ p) / 2) ^ p⁻¹ ≤
      ((‖a + b‖ ^ (p / (p - 1)) + ‖a - b‖ ^ (p / (p - 1))) / 2) ^ (p / (p - 1))⁻¹ := by sorry
