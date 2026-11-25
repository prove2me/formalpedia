-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_forcing
-- name    : LeanPool.ListEdgeColoringComplete.forcing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:15:04.771299+00:00
-- url     : https://prove2.me/theorems/e51e8b9d-3481-46cd-9ba7-7d4300f04f46
-- title:
--   List Edge Coloring Complete: forcing
-- statement:
--   **Forced choice.** This is the arithmetic heart of the uniqueness argument of
--   pages 305--306. Let `{a, b}` be an edge with low end `b`. Suppose that some other edge
--   `{a, l}`, not processed before `{a, b}`, received the rank of `{a, b}` in `C_a`; then
--   the complementary rank at `l` is already used in `C_l` by an edge `{l, x}` that *was*
--   processed before `{a, b}`.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L173-L239
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L173-L239

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}

theorem LeanPool.ListEdgeColoringComplete.forcing {a b l x : ℕ} (ha : a < n) (hb : b < n) (hl : l < n) (hx : x < n)
    (hab : ¬ IsLowEnd n a b) (hlb : l ≠ b) (hxl : x ≠ l) (hxa : x ≠ a)
    (hk : ¬ Precedes n a l a b)
    (hsum : localRank n l x + localRank n a b = targetDegree n a l) :
    Precedes n l x a b := by sorry
