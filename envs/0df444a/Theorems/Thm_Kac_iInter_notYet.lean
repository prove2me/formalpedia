-- Prove2me | Theorems.Thm_Kac_iInter_notYet
-- name    : Kac.iInter_notYet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:04:15.473811+00:00
-- url     : https://prove2.me/theorems/fa7d9746-2a3f-5cd3-82ae-3e4f72664395
-- title:
--   Kac: i Inter not Yet
-- statement:
--   The points that never meet `A` are the complement of the points that meet it at some time.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L115-L122
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L115-L122

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

theorem Kac.iInter_notYet : ⋂ n, notYet f A n = (⋃ k : ℕ, f^[k] ⁻¹' A)ᶜ := by sorry
