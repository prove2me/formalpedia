-- Prove2me | Theorems.Thm_GrahamPollak_exists_bicliqueDecomposition
-- name    : GrahamPollak.exists_bicliqueDecomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:29.344636+00:00
-- url     : https://prove2.me/theorems/3a9db85c-a536-4aed-b6c5-07324a13b524
-- title:
--   Graham Pollak: exists biclique Decomposition
-- statement:
--   The Graham–Pollak bound is attained: `K_n` (`n ≥ 1`) is the union of `n − 1` stars.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L147-L160
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L147-L160

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}

theorem GrahamPollak.exists_bicliqueDecomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B := by sorry
