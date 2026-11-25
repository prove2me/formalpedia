-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_injective
-- name    : LeanPool.ListEdgeColoringComplete.canonicalRow_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:03.768694+00:00
-- url     : https://prove2.me/theorems/3adb83b9-588a-411e-b2e0-6c36d55b73e6
-- title:
--   List Edge Coloring Complete: canonical Row injective
-- statement:
--   The List Edge Coloring Complete construction uses the canonical Row injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L253-L255
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L253-L255

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n : ℕ}

theorem LeanPool.ListEdgeColoringComplete.canonicalRow_injective (i : Fin n) : Function.Injective (canonicalRow i) := by sorry
