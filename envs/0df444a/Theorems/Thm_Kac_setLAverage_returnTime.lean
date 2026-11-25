-- Prove2me | Theorems.Thm_Kac_setLAverage_returnTime
-- name    : Kac.setLAverage_returnTime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:23:58.238976+00:00
-- url     : https://prove2.me/theorems/236fa20d-4355-5715-906c-3a35186f7616
-- title:
--   Kac: set LAverage return Time
-- statement:
--   **The mean return time to `A` is `1 / μ A`.** For an ergodic map of a probability space and
--   `μ A ≠ 0`, the average of the return time over `A` is `(μ A)⁻¹`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L461-L463
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L461-L463

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

theorem Kac.setLAverage_returnTime (hf : Ergodic f μ) (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ⨍⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = (μ A)⁻¹ := by sorry
