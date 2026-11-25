-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_certificate_unique
-- name    : LeanPool.ListEdgeColoringComplete.certificate_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:15:05.364927+00:00
-- url     : https://prove2.me/theorems/363b3ebc-9ccc-575f-865d-8553b6e88d3f
-- title:
--   List Edge Coloring Complete: certificate unique
-- statement:
--   **Uniqueness of the certificate.** Any family of rank rows (one bijection
--   `Fin n → Fin n` per extended star clique) that gives the artificial vertex of `C_i` its
--   blocked value and whose two local ranks at each edge add up to `ρ` is the canonical one.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L272-L355
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L272-L355

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

theorem LeanPool.ListEdgeColoringComplete.certificate_unique (r : Fin n → Fin n → Fin n)
    (hinj : ∀ i, Function.Injective (r i))
    (hdiag : ∀ i, (r i i : ℕ) = blockedRank n i)
    (hsum : ∀ i j, i ≠ j → (r i j : ℕ) + r j i = targetDegree n i j) :
    r = canonicalRow := by sorry
