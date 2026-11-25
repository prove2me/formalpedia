-- Prove2me | Theorems.Thm_Kac_notYet_succ
-- name    : Kac.notYet_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:08.343925+00:00
-- url     : https://prove2.me/theorems/d1184f66-3935-55ca-9e23-2ec9acbcda1c
-- title:
--   Kac: not Yet succ
-- statement:
--   The Kac construction uses the not Yet succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L90-L90
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L90-L90

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

theorem Kac.notYet_succ (n : ℕ) : notYet f A (n + 1) = Aᶜ ∩ f ⁻¹' notYet f A n := by sorry

attribute [defeq] Kac.notYet_succ
