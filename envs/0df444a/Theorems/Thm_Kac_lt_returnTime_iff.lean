-- Prove2me | Theorems.Thm_Kac_lt_returnTime_iff
-- name    : Kac.lt_returnTime_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:07:33.019377+00:00
-- url     : https://prove2.me/theorems/7cc1636d-c230-5fa9-b7fc-f1becb7d0f65
-- title:
--   Kac: lt return Time iff
-- statement:
--   Starting anywhere, the first return time exceeds `n` exactly when the iterates of `x` at times
--   `1, …, n` all miss `A`, that is, when `f x ∈ notYet f A n`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L128-L153
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L128-L153

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

theorem Kac.lt_returnTime_iff (n : ℕ) (x : α) :
    (n : ℕ∞) < returnTime f A x ↔ f x ∈ notYet f A n := by sorry
