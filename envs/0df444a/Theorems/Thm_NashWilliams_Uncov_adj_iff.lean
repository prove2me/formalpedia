-- Prove2me | Theorems.Thm_NashWilliams_Uncov_adj_iff
-- name    : NashWilliams.Uncov.adj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:40:55.172822+00:00
-- url     : https://prove2.me/theorems/b36e045d-cdb8-4f5a-88a6-96fec778e7fa
-- title:
--   Uncov: adj iff
-- statement:
--   The Uncov construction uses the adj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L200-L204
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L200-L204

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

theorem NashWilliams.Uncov.adj_iff {F : Fin k → SimpleGraph V} {u v : V} (h : Uncov G F u v) {j : Fin k}
    {a b : V} (hab : s(a, b) = s(u, v)) : ¬ (F j).Adj a b := by sorry
