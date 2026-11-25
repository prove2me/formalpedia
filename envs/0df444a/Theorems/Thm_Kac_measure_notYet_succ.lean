-- Prove2me | Theorems.Thm_Kac_measure_notYet_succ
-- name    : Kac.measure_notYet_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:38.392596+00:00
-- url     : https://prove2.me/theorems/3caa5142-1ef9-48b1-9fc6-1b74836c05b5
-- title:
--   Kac: measure not Yet succ
-- statement:
--   The preimage of `notYet n` splits into the points of `A` that have not returned within `n`
--   steps, and `notYet (n+1)`; measure preservation identifies its measure with `μ (notYet n)`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L254-L267
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L254-L267

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

theorem Kac.measure_notYet_succ (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (n : ℕ) :
    μ (notYet f A n) = μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A (n + 1)) := by sorry
