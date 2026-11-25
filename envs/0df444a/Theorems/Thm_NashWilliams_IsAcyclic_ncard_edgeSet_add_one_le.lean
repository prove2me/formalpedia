-- Prove2me | Theorems.Thm_NashWilliams_IsAcyclic_ncard_edgeSet_add_one_le
-- name    : NashWilliams.IsAcyclic.ncard_edgeSet_add_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:40:49.140205+00:00
-- url     : https://prove2.me/theorems/891b3519-2404-58f5-83ef-d1168fec3496
-- title:
--   Is Acyclic: ncard edge Set add one le
-- statement:
--   A forest on a finite nonempty vertex type has at most `|V| - 1` edges, and exactly `|V| - 1`
--   only if it is a tree.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L66-L79
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L66-L79

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.IsAcyclic.ncard_edgeSet_add_one_le [Finite V] [Nonempty V] {F : SimpleGraph V}
    (hF : F.IsAcyclic) :
    F.edgeSet.ncard + 1 ≤ Nat.card V ∧ (Nat.card V ≤ F.edgeSet.ncard + 1 → F.IsTree) := by sorry
