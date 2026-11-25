-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_spec
-- name    : LeanPool.ListEdgeColoringComplete.canonicalRow_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:07.197148+00:00
-- url     : https://prove2.me/theorems/9c69b26e-f1b1-5019-96eb-dd627e707078
-- title:
--   List Edge Coloring Complete: canonical Row spec
-- statement:
--   **Existence**: the canonical rows form a certificate.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L258-L267
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L258-L267

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

theorem LeanPool.ListEdgeColoringComplete.canonicalRow_spec :
    (∀ i : Fin n, Function.Injective (canonicalRow i)) ∧
    (∀ i : Fin n, (canonicalRow i i : ℕ) = blockedRank n i) ∧
    (∀ i j : Fin n, i ≠ j →
      (canonicalRow i j : ℕ) + canonicalRow j i = targetDegree n i j) := by sorry
