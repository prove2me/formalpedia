-- Prove2me | Theorems.Thm_NashWilliams_card_image_le_ncard_crossing_add_one
-- name    : NashWilliams.card_image_le_ncard_crossing_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:42.547059+00:00
-- url     : https://prove2.me/theorems/d63a8f45-47dc-5433-bc44-60e7216278d0
-- title:
--   Nash Williams: card image le ncard crossing add one
-- statement:
--   A connected graph has at least `m - 1` edges joining different fibres of `f`, where `m` is the
--   number of nonempty fibres.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L116-L151
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L116-L151

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.card_image_le_ncard_crossing_add_one [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hT : T.Connected) (f : V → V) :
    #(univ.image f) ≤ (T.edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard + 1 := by sorry
