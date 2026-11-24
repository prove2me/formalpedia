-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_length15_singleton_unique
-- name    : InverseZeroSum.Candidate3.length15_singleton_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:40.649808+00:00
-- url     : https://prove2.me/theorems/8989df34-b91a-4656-bf88-9cab3a53b4cb
-- title:
--   Candidate3: length15 singleton unique
-- statement:
--   The fibre of multiplicity one is unique.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2650-L2667
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2650-L2667

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.length15_singleton_unique
    (R : PosSeq 15) (hFree : ShortFree R)
    {u : F3T} (hu : u ∈ tupleSupportT R)
    (huOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1)
    {v : F3T} (hv : v ∈ tupleSupportT R)
    (hvOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = v)).card = 1) :
    v = u := by sorry
