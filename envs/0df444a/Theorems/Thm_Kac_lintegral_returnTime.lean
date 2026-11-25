-- Prove2me | Theorems.Thm_Kac_lintegral_returnTime
-- name    : Kac.lintegral_returnTime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:18:00.148801+00:00
-- url     : https://prove2.me/theorems/902773e6-308f-5a45-99a2-e05a4d96d46d
-- title:
--   Kac: lintegral return Time
-- statement:
--   **Kac's formula, for any measure.** For a measure-preserving map, the integral of the return
--   time over `A` is the measure of the points that ever meet `A`. No finiteness, conservativity or
--   ergodicity is assumed.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L360-L362
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L360-L362

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

theorem Kac.lintegral_returnTime (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by sorry
