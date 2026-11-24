-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_update_split
-- name    : InverseZeroSum.Candidate3.representativeSet_update_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:47.617067+00:00
-- url     : https://prove2.me/theorems/5c811ed9-9176-4e1d-a509-6946cc1aeab0
-- title:
--   Candidate3: representative Set update split
-- statement:
--   The representative set after updating one block has an explicit split.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2830-L2857
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2830-L2857

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.representativeSet_update_split {s : ℕ}
    (base : Fin s → Fin 24) (j : Fin s) (z : Fin 24) :
    representativeSet (Function.update base j z) =
      insert z (((Finset.univ : Finset (Fin s)).erase j).image base) := by sorry
