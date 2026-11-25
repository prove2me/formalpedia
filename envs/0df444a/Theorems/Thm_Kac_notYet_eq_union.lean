-- Prove2me | Theorems.Thm_Kac_notYet_eq_union
-- name    : Kac.notYet_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:07:50.266871+00:00
-- url     : https://prove2.me/theorems/39473c4e-5a0b-51db-88d9-597b484b9c88
-- title:
--   Kac: not Yet eq union
-- statement:
--   The Kac construction uses the not Yet eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L200-L201
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L200-L201

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

theorem Kac.notYet_eq_union (n : ℕ) : notYet f A n = firstHit f A n ∪ notYet f A (n + 1) := by sorry
