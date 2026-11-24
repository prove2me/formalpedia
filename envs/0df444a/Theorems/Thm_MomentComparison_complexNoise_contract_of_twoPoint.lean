-- Prove2me | Theorems.Thm_MomentComparison_complexNoise_contract_of_twoPoint
-- name    : MomentComparison.complexNoise_contract_of_twoPoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:54:17.731501+00:00
-- url     : https://prove2.me/theorems/60fa14b2-e9aa-497c-bd4f-3fa42d8baf50
-- title:
--   Moment Comparison: complex Noise contract of two Point
-- statement:
--   Iterating the two-point noise inequality on the cube, with Minkowski
--   interchanging the inner and outer moments.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Hypercontractivity.lean#L106-L164
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Hypercontractivity.lean#L106-L164

module
public import Definitions.Def_MomentComparison_MomentNorm
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Definitions.Def_MomentComparison_TwoPointReduction
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Hypercontractivity
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.complexNoise_contract_of_twoPoint {p q : ℝ} {w : ℂ} (hq : 0 < q) (hqp : q ≤ p)
    (htwo : ∀ a b : ℂ,
      ((‖a + w * b‖ ^ p + ‖a - w * b‖ ^ p) / 2) ^ p⁻¹ ≤
        ((‖a + b‖ ^ q + ‖a - b‖ ^ q) / 2) ^ q⁻¹)
    {n : ℕ} (f : Cube n → ℂ) :
    complexMomentNorm p (complexNoise w f) ≤ complexMomentNorm q f := by sorry
