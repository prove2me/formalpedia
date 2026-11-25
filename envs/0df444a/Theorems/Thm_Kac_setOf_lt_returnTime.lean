-- Prove2me | Theorems.Thm_Kac_setOf_lt_returnTime
-- name    : Kac.setOf_lt_returnTime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:04:40.833989+00:00
-- url     : https://prove2.me/theorems/f3609303-ca37-4392-86b8-d68598f1000e
-- title:
--   Kac: set Of lt return Time
-- statement:
--   The Kac construction uses the set Of lt return Time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L155-L158
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L155-L158

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

theorem Kac.setOf_lt_returnTime (n : ℕ) :
    {x | (n : ℕ∞) < returnTime f A x} = f ⁻¹' notYet f A n := by sorry
