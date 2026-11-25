-- Prove2me | Theorems.Thm_NashWilliams_card_le_ncard_edgeSet_add_card_image
-- name    : NashWilliams.card_le_ncard_edgeSet_add_card_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:50.945694+00:00
-- url     : https://prove2.me/theorems/22dd6021-0b7d-4f98-a97d-351f4603a05d
-- title:
--   Nash Williams: card le ncard edge Set add card image
-- statement:
--   If every vertex `v` is reachable in `K` from `f v`, then `K` has at least
--   `|V| - #(image f)` edges.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L83-L112
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L83-L112

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.card_le_ncard_edgeSet_add_card_image [Fintype V] [DecidableEq V] [Nonempty V]
    (K : SimpleGraph V) (f : V → V) (hf : ∀ v, K.Reachable v (f v)) :
    Nat.card V ≤ K.edgeSet.ncard + #(univ.image f) := by sorry
