-- Prove2me | Theorems.Thm_Kac_measurableSet_notYet
-- name    : Kac.measurableSet_notYet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:17.475301+00:00
-- url     : https://prove2.me/theorems/e88438aa-2976-5504-bde3-ff49f9b0e92c
-- title:
--   Kac: measurable Set not Yet
-- statement:
--   The Kac construction uses the measurable Set not Yet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L240-L243
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L240-L243

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

theorem Kac.measurableSet_notYet (hf : Measurable f) (hA : MeasurableSet A) :
    ∀ n, MeasurableSet (notYet f A n)
  := by sorry
