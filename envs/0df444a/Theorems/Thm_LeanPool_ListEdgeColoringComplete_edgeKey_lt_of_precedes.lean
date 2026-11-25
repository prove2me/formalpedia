-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_edgeKey_lt_of_precedes
-- name    : LeanPool.ListEdgeColoringComplete.edgeKey_lt_of_precedes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:14:50.146029+00:00
-- url     : https://prove2.me/theorems/ca61ee69-aae8-597f-ae19-a1eadddb548e
-- title:
--   List Edge Coloring Complete: edge Key lt of precedes
-- statement:
--   The List Edge Coloring Complete construction uses the edge Key lt of precedes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L116-L127
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L116-L127

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

theorem LeanPool.ListEdgeColoringComplete.edgeKey_lt_of_precedes {u' v' : ℕ} (hu : u < n) (hv : v < n) (hu' : u' < n)
    (hv' : v' < n) (h : Precedes n u v u' v') : edgeKey n u v < edgeKey n u' v' := by sorry
