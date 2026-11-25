-- Prove2me | Theorems.Thm_Kac_firstHit_zero
-- name    : Kac.firstHit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:15:14.088127+00:00
-- url     : https://prove2.me/theorems/5c1fea74-ff89-4ed6-8fb7-4ef8b80956fe
-- title:
--   Kac: first Hit zero
-- statement:
--   The Kac construction uses the first Hit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L207-L208
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L207-L208

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
variable {α : Type*} {f : α → α} {A : Set α}

theorem Kac.firstHit_zero : firstHit f A 0 = A := by sorry
