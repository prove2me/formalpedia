-- Prove2me | Theorems.Thm_Kac_tsum_measure_lt_returnTime
-- name    : Kac.tsum_measure_lt_returnTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:45.195336+00:00
-- url     : https://prove2.me/theorems/02e8e0aa-b906-4639-bdd9-4d08e898ca0d
-- title:
--   Kac: tsum measure lt return Time
-- statement:
--   **Kac's formula as a series, for any measure.** For any measure-preserving map,
--   `∑ₙ μ {x ∈ A : n < n_A x} = μ (⋃ k, f^[k] ⁻¹' A)`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L343-L355
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L343-L355

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

theorem Kac.tsum_measure_lt_returnTime (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) :
    ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by sorry
