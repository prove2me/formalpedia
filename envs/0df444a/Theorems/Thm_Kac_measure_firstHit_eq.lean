-- Prove2me | Theorems.Thm_Kac_measure_firstHit_eq
-- name    : Kac.measure_firstHit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:55.197531+00:00
-- url     : https://prove2.me/theorems/c2e4d561-9e2f-4be0-adcc-08e130f7fe41
-- title:
--   Kac: measure first Hit eq
-- statement:
--   **The key step.** If `μ A < ∞`, the points that first meet `A` at time `n` have the same measure
--   as the points of `A` that have not returned within `n` steps. Both start at `μ A`, and each step
--   removes the points of `A` that return at time `n + 1`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L309-L339
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L309-L339

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

theorem Kac.measure_firstHit_eq (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (n : ℕ) : μ (firstHit f A n) = μ (A ∩ f ⁻¹' notYet f A n) := by sorry
