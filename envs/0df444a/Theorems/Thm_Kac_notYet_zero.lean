-- Prove2me | Theorems.Thm_Kac_notYet_zero
-- name    : Kac.notYet_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:21.633442+00:00
-- url     : https://prove2.me/theorems/c4ed5e44-5f97-46aa-a755-3cf8abee0f9f
-- title:
--   Kac: not Yet zero
-- statement:
--   The Kac construction uses the not Yet zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L88-L88
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L88-L88

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

theorem Kac.notYet_zero : notYet f A 0 = univ := by sorry

attribute [defeq] Kac.notYet_zero
