-- Prove2me | Theorems.Thm_Kac_measure_iInter_notYet_eq_zero
-- name    : Kac.measure_iInter_notYet_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:49:25.538648+00:00
-- url     : https://prove2.me/theorems/61781e0f-7c5d-418a-9868-15fed2e238b1
-- title:
--   Kac: measure i Inter not Yet eq zero
-- statement:
--   For an ergodic map of a finite measure space and `μ A ≠ 0`, almost every point meets `A`.
--   Finiteness is used only through `MeasurePreserving.conservative` (Poincaré recurrence).
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L401-L437
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L401-L437

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

theorem Kac.measure_iInter_notYet_eq_zero (hf : Ergodic f μ) (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    μ (⋂ n, notYet f A n) = 0 := by sorry
