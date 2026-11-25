-- Prove2me | Theorems.Thm_Kac_sum_measure_inter_notYet
-- name    : Kac.sum_measure_inter_notYet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:33.892831+00:00
-- url     : https://prove2.me/theorems/a5dbe061-e058-401d-86e8-b818ee961fd3
-- title:
--   Kac: sum measure inter not Yet
-- statement:
--   The telescoped partial sums. The sum is the integral over `A` of the return time truncated at
--   `N`, `∫ x in A, min (n_A x) N`; adding the measure of the points that miss `A` at times
--   `0, …, N-1` gives everything.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L272-L278
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L272-L278

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

theorem Kac.sum_measure_inter_notYet (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (N : ℕ) :
    ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A N) = μ univ := by sorry
