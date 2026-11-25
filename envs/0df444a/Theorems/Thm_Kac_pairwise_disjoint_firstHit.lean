-- Prove2me | Theorems.Thm_Kac_pairwise_disjoint_firstHit
-- name    : Kac.pairwise_disjoint_firstHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:08:09.707807+00:00
-- url     : https://prove2.me/theorems/90d0412d-f22f-49cc-b6e5-d4b2f9579ec4
-- title:
--   Kac: pairwise disjoint first Hit
-- statement:
--   The Kac construction uses the pairwise disjoint first Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L215-L220
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L215-L220

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

theorem Kac.pairwise_disjoint_firstHit :
    Pairwise fun m n : ℕ => Disjoint (firstHit f A m) (firstHit f A n) := by sorry
