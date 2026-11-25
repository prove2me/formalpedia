-- Prove2me | Theorems.Thm_Kac_mem_notYet_iff
-- name    : Kac.mem_notYet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:11.390807+00:00
-- url     : https://prove2.me/theorems/b2e9c70c-d4f4-5353-bd2e-ffb86d91d47c
-- title:
--   Kac: mem not Yet iff
-- statement:
--   The Kac construction uses the mem not Yet iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L92-L107
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L92-L107

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

theorem Kac.mem_notYet_iff (n : ℕ) (x : α) : x ∈ notYet f A n ↔ ∀ k < n, f^[k] x ∉ A := by sorry
