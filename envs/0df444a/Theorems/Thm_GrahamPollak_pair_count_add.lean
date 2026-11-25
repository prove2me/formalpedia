-- Prove2me | Theorems.Thm_GrahamPollak_pair_count_add
-- name    : GrahamPollak.pair_count_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:44.74243+00:00
-- url     : https://prove2.me/theorems/79249d53-4d3e-4b05-b38a-97f5c80ee38c
-- title:
--   Graham Pollak: pair count add
-- statement:
--   The Graham Pollak construction uses the pair count add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L41-L66
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L41-L66

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]

theorem GrahamPollak.pair_count_add {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (u v : V) :
    (∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ))) +
      (∑ i, ((if v ∈ A i ∧ u ∈ B i then 1 else 0 : ℝ))) = if u = v then 0 else 1 := by sorry
