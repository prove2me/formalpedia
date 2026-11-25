-- Prove2me | Theorems.Thm_GrahamPollakTheorem_exists_bicliqueDecomposition
-- name    : GrahamPollakTheorem.exists_bicliqueDecomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:54.763135+00:00
-- url     : https://prove2.me/theorems/89d536e3-4005-4af5-bb0c-d30855bb2744
-- title:
--   Graham Pollak Theorem: exists biclique Decomposition
-- statement:
--   The Graham–Pollak bound is attained: `K_n` (`n ≥ 1`) is the union of `n − 1` stars.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/Solution.lean#L41-L43
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/Solution.lean#L41-L43

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Definitions.Def_GrahamPollak_Solution
public import Theorems.Thm_GrahamPollak_exists_bicliqueDecomposition

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollakTheorem
variable {V : Type*}

theorem GrahamPollakTheorem.exists_bicliqueDecomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B := by sorry
