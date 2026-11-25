-- Prove2me | Theorems.Thm_Kac_iUnion_firstHit
-- name    : Kac.iUnion_firstHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:11:16.104915+00:00
-- url     : https://prove2.me/theorems/904664bc-8765-42c1-9931-c612d232c29e
-- title:
--   Kac: i Union first Hit
-- statement:
--   The sets `firstHit n` cover exactly the points that ever meet `A`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L223-L231
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L223-L231

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

theorem Kac.iUnion_firstHit : ⋃ n, firstHit f A n = ⋃ k : ℕ, f^[k] ⁻¹' A := by sorry
