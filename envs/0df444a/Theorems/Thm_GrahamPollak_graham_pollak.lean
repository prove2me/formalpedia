-- Prove2me | Theorems.Thm_GrahamPollak_graham_pollak
-- name    : GrahamPollak.graham_pollak
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:26.364596+00:00
-- url     : https://prove2.me/theorems/1dbf8d2c-5fc8-41bc-a113-cedd4ba81192
-- title:
--   Graham Pollak: graham pollak
-- statement:
--   **Graham–Pollak (1971).** The complete graph on `n` vertices cannot be decomposed into fewer
--   than `n − 1` complete bipartite graphs.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L114-L144
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L114-L144

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}

theorem GrahamPollak.graham_pollak [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m := by sorry
