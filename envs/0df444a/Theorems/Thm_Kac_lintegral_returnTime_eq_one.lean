-- Prove2me | Theorems.Thm_Kac_lintegral_returnTime_eq_one
-- name    : Kac.lintegral_returnTime_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:15:02.768479+00:00
-- url     : https://prove2.me/theorems/140a3837-8815-4e75-9b74-c8de84801d86
-- title:
--   Kac: lintegral return Time eq one
-- statement:
--   **Kac's formula.** For an ergodic map of a probability space and `μ A ≠ 0`, the integral of the
--   return time over `A` is `1`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L449-L457
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L449-L457

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
variable [IsProbabilityMeasure μ]

theorem Kac.lintegral_returnTime_eq_one (hf : Ergodic f μ) (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = 1 := by sorry
