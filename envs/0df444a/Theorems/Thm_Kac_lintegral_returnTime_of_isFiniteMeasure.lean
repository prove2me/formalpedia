-- Prove2me | Theorems.Thm_Kac_lintegral_returnTime_of_isFiniteMeasure
-- name    : Kac.lintegral_returnTime_of_isFiniteMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:23:56.114154+00:00
-- url     : https://prove2.me/theorems/f760528c-d5e7-564d-8f2f-dcee5765e1fc
-- title:
--   Kac: lintegral return Time of is Finite Measure
-- statement:
--   **Kac's formula for a finite measure**, by the telescope: the integral of the return time over
--   `A` is the measure of the points that ever meet `A`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L391-L395
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L391-L395

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
variable [IsFiniteMeasure μ]

theorem Kac.lintegral_returnTime_of_isFiniteMeasure (hf : MeasurePreserving f μ μ)
    (hA : MeasurableSet A) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by sorry
