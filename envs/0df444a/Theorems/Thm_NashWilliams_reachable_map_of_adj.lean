-- Prove2me | Theorems.Thm_NashWilliams_reachable_map_of_adj
-- name    : NashWilliams.reachable_map_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:40:46.306496+00:00
-- url     : https://prove2.me/theorems/e5a4b1de-cce9-4d85-967f-35c9cf240227
-- title:
--   Nash Williams: reachable map of adj
-- statement:
--   Reachability transfers along a map that sends adjacent vertices to reachable ones.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L28-L34
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L28-L34

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.reachable_map_of_adj {W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (g : V → W)
    (h : ∀ a b, A.Adj a b → B.Reachable (g a) (g b)) {a b : V} (hab : A.Reachable a b) :
    B.Reachable (g a) (g b) := by sorry
