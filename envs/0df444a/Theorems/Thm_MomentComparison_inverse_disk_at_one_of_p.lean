-- Prove2me | Theorems.Thm_MomentComparison_inverse_disk_at_one_of_p
-- name    : MomentComparison.inverse_disk_at_one_of_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:22:23.332828+00:00
-- url     : https://prove2.me/theorems/981a69e6-d69d-4090-894b-664e399b3793
-- title:
--   Moment Comparison: inverse disk at one of p
-- statement:
--   The inverse map at the parameter representing evaluation at 1.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensEvaluation.lean#L172-L184
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensEvaluation.lean#L172-L184

module
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_LensEvaluation
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.inverse_disk_at_one_of_p {p : ℝ} (hp : 2 < p) :
    let r := Real.sqrt (p - 1)
    let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
    let z := Complex.I * (r : ℂ)
    let a := (z - 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let b := (z + 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let t := (a - b) / (a + b)
    ‖t‖ < 1 ∧ t ≠ 0 ∧
      ((1 - t) ^ (β : ℂ) + (1 + t) ^ (β : ℂ)) /
        ((1 - t) ^ (β : ℂ) - (1 + t) ^ (β : ℂ)) / z = 1 := by sorry
