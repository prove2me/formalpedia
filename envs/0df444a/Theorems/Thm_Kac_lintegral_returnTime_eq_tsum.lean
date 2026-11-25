-- Prove2me | Theorems.Thm_Kac_lintegral_returnTime_eq_tsum
-- name    : Kac.lintegral_returnTime_eq_tsum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:04:49.116459+00:00
-- url     : https://prove2.me/theorems/f843f0dd-f4ed-4747-821e-7386d8e98b27
-- title:
--   Kac: lintegral return Time eq tsum
-- statement:
--   The integral of the return time over `A` is the series `∑ₙ μ {x ∈ A : n < n_A x}`, for any
--   measure: the tail-sum formula, integrated.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L284-L302
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L284-L302

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

theorem Kac.lintegral_returnTime_eq_tsum (hf : Measurable f) (hA : MeasurableSet A) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ
      = ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) := by sorry
