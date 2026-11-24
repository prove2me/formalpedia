-- Prove2me | Theorems.Thm_MomentComparison_anisotropic_sq_le
-- name    : MomentComparison.anisotropic_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:23.153947+00:00
-- url     : https://prove2.me/theorems/087da6c9-e26b-4ba3-8930-179c8a8b8f58
-- title:
--   Moment Comparison: anisotropic sq le
-- statement:
--   Membership in the lens guarantees the quadratic inequality obtained by
--   expanding the two-point noise inequality at a constant function.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lens.lean#L67-L131
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lens.lean#L67-L131

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Lens
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.anisotropic_sq_le {p : ℝ} (hp : 2 < p) {w z : ℂ} (hw : inLens p w) :
    (p - 1) * (w * z).re ^ 2 + (w * z).im ^ 2 ≤
      (p - 1)⁻¹ * z.re ^ 2 + z.im ^ 2 := by sorry
