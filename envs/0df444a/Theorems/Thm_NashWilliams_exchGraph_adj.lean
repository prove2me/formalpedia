-- Prove2me | Theorems.Thm_NashWilliams_exchGraph_adj
-- name    : NashWilliams.exchGraph_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:41:16.717538+00:00
-- url     : https://prove2.me/theorems/c3524d66-0d9e-4b87-882b-368508f449f8
-- title:
--   Nash Williams: exch Graph adj
-- statement:
--   The Nash Williams construction uses the exch Graph adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L321-L323
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L321-L323

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable {G : SimpleGraph V} {k : ℕ}

theorem NashWilliams.exchGraph_adj {F₀ : Fin k → SimpleGraph V} {a b : V} :
    (exchGraph G F₀).Adj a b ↔ ∃ F, Relation.ReflTransGen (Step G) F₀ F ∧ Uncov G F a b := by sorry
