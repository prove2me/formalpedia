-- Prove2me | Theorems.Thm_List_toFinset_eq_image_of_length_eq_card
-- name    : List.toFinset_eq_image_of_length_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:25.375051+00:00
-- url     : https://prove2.me/theorems/d8e0706c-bd7f-41ce-8505-3bfc3e0c829e
-- title:
--   List: to Finset eq image of length eq card
-- statement:
--   If `l` has no repetitions, every member of `l` is `g x` for some `x ∈ S`, `g` is injective and
--   `l` has as many members as `S` has elements, then the members of `l` are exactly the `g x` with
--   `x ∈ S`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L260-L267
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L260-L267

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
set_option autoImplicit false
public section
open List
variable {α β : Type*}

theorem List.toFinset_eq_image_of_length_eq_card [DecidableEq β] (l : List β) (hl : l.Nodup)
    (S : Finset α) (g : α → β)
    (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y) (hcard : l.length = S.card) :
    l.toFinset = S.image g := by sorry
