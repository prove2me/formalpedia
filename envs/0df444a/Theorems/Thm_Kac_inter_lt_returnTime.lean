-- Prove2me | Theorems.Thm_Kac_inter_lt_returnTime
-- name    : Kac.inter_lt_returnTime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:04:39.316437+00:00
-- url     : https://prove2.me/theorems/391d7dcd-c027-4da8-b5ef-9473b08eade1
-- title:
--   Kac: inter lt return Time
-- statement:
--   The Kac construction uses the inter lt return Time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L160-L162
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L160-L162

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

theorem Kac.inter_lt_returnTime (n : ℕ) :
    A ∩ {x | (n : ℕ∞) < returnTime f A x} = A ∩ f ⁻¹' notYet f A n := by sorry
