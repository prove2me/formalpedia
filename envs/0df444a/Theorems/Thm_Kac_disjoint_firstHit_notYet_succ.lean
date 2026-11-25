-- Prove2me | Theorems.Thm_Kac_disjoint_firstHit_notYet_succ
-- name    : Kac.disjoint_firstHit_notYet_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:07:56.785418+00:00
-- url     : https://prove2.me/theorems/a0a5b3c2-b01a-5310-9249-02614adf8784
-- title:
--   Kac: disjoint first Hit not Yet succ
-- statement:
--   The Kac construction uses the disjoint first Hit not Yet succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L203-L205
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L203-L205

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

theorem Kac.disjoint_firstHit_notYet_succ (n : ℕ) : Disjoint (firstHit f A n) (notYet f A (n + 1)) := by sorry
