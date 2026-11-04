-- Prove2me | Theorems.Thm_List_sum_map_eq_sum_of_length_eq_card
-- name    : List.sum_map_eq_sum_of_length_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:24.881206+00:00
-- url     : https://prove2.me/theorems/e7930f38-a595-4e69-af3e-c85f2953869b
-- title:
--   List: sum map eq sum of length eq card
-- statement:
--   Under the same hypotheses, a sum over `l` is a sum over `S`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L270-L276
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L270-L276

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

theorem List.sum_map_eq_sum_of_length_eq_card {M : Type*} [AddCommMonoid M] (l : List β) (hl : l.Nodup)
    (S : Finset α)
    (g : α → β) (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y)
    (hcard : l.length = S.card) (F : β → M) : (l.map F).sum = ∑ x ∈ S, F (g x) := by sorry
