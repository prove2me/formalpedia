-- Prove2me | Theorems.Thm_GrahamPollakTheorem_graham_pollak
-- name    : GrahamPollakTheorem.graham_pollak
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:30:01.864593+00:00
-- url     : https://prove2.me/theorems/2d99626d-af4f-4a09-9ad9-9b5c67c4fba6
-- title:
--   Graham Pollak Theorem: graham pollak
-- statement:
--   **Graham–Pollak (1971).** The complete graph on `n` vertices cannot be decomposed into fewer
--   than `n − 1` complete bipartite graphs.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/Solution.lean#L36-L38
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/Solution.lean#L36-L38

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Definitions.Def_GrahamPollak_Solution
public import Theorems.Thm_GrahamPollak_graham_pollak

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollakTheorem
variable {V : Type*}

theorem GrahamPollakTheorem.graham_pollak [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m := by sorry
