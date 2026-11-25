-- Prove2me | Theorems.Thm_Kac_firstHit_succ
-- name    : Kac.firstHit_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:08:11.288334+00:00
-- url     : https://prove2.me/theorems/e56c935a-d266-447b-ad79-0ab4b14aa3b0
-- title:
--   Kac: first Hit succ
-- statement:
--   The Kac construction uses the first Hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L210-L213
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L210-L213

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

theorem Kac.firstHit_succ (n : ℕ) : firstHit f A (n + 1) = Aᶜ ∩ f ⁻¹' firstHit f A n := by sorry
