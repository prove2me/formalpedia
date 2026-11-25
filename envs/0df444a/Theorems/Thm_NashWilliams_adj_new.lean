-- Prove2me | Theorems.Thm_NashWilliams_adj_new
-- name    : NashWilliams.adj_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:40:39.995411+00:00
-- url     : https://prove2.me/theorems/32e78c11-3a26-5ca5-864a-f2a625bd1525
-- title:
--   Nash Williams: adj new
-- statement:
--   The Nash Williams construction uses the adj new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L206-L216
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L206-L216

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}

theorem NashWilliams.adj_new {F : SimpleGraph V} {x y u v a b : V}
    (h : (F.deleteEdges {s(x, y)} ⊔ edge u v).Adj a b) :
    (F.Adj a b ∧ s(a, b) ≠ s(x, y)) ∨ s(a, b) = s(u, v) := by sorry
