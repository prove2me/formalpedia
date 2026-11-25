-- Prove2me | Theorems.Thm_Kac_antitone_notYet
-- name    : Kac.antitone_notYet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:07:30.766201+00:00
-- url     : https://prove2.me/theorems/280e74b2-5c01-4b92-9453-633def189bec
-- title:
--   Kac: antitone not Yet
-- statement:
--   The Kac construction uses the antitone not Yet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L109-L112
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L109-L112

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

theorem Kac.antitone_notYet : Antitone (notYet f A) := by sorry
