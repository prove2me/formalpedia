-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_filter_card_exchange
-- name    : InverseZeroSum.Candidate3.filter_card_exchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:32.288911+00:00
-- url     : https://prove2.me/theorems/e8c1697e-344e-4544-af53-5154917e0eca
-- title:
--   Candidate3: filter card exchange
-- statement:
--   Purely positional fibre-count exchange: remove an old position y, insert an
--   absent position x, and compare each fibre.  The symmetric addition form avoids
--   truncated natural-number subtraction and retains the exact two-value change.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2806-L2825
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2806-L2825

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.filter_card_exchange
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) {x y : α}
    (hx : x ∉ A) (hy : y ∈ A) (v : β) :
    ((insert x (A.erase y)).filter (fun z => f z = v)).card +
        (if f y = v then 1 else 0) =
      (A.filter (fun z => f z = v)).card +
        (if f x = v then 1 else 0) := by sorry
