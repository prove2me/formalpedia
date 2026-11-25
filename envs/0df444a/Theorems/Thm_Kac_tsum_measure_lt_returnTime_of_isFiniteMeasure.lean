-- Prove2me | Theorems.Thm_Kac_tsum_measure_lt_returnTime_of_isFiniteMeasure
-- name    : Kac.tsum_measure_lt_returnTime_of_isFiniteMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:48.550228+00:00
-- url     : https://prove2.me/theorems/e6530271-7ed5-5377-a243-a78b39df8f6e
-- title:
--   Kac: tsum measure lt return Time of is Finite Measure
-- statement:
--   Kac's formula as a series for a finite measure, proved by telescoping from the whole space.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L371-L387
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L371-L387

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

theorem Kac.tsum_measure_lt_returnTime_of_isFiniteMeasure (hf : MeasurePreserving f μ μ)
    (hA : MeasurableSet A) :
    ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by sorry
