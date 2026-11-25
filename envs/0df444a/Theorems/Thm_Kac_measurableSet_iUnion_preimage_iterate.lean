-- Prove2me | Theorems.Thm_Kac_measurableSet_iUnion_preimage_iterate
-- name    : Kac.measurableSet_iUnion_preimage_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:23.852279+00:00
-- url     : https://prove2.me/theorems/40d65512-c273-5168-8d6a-e2e221fd9065
-- title:
--   Kac: measurable Set i Union preimage iterate
-- statement:
--   The points that ever meet `A` form a measurable set.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L246-L248
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L246-L248

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

theorem Kac.measurableSet_iUnion_preimage_iterate (hf : Measurable f) (hA : MeasurableSet A) :
    MeasurableSet (⋃ k : ℕ, f^[k] ⁻¹' A) := by sorry
