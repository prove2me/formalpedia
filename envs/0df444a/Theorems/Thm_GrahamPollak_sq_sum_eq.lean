-- Prove2me | Theorems.Thm_GrahamPollak_sq_sum_eq
-- name    : GrahamPollak.sq_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:53.684785+00:00
-- url     : https://prove2.me/theorems/66300228-63ec-46be-91bc-9ffba02f89da
-- title:
--   Graham Pollak: sq sum eq
-- statement:
--   The Graham Pollak construction uses the sq sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L83-L108
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L83-L108

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]

theorem GrahamPollak.sq_sum_eq [Fintype V] {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (x : V → ℝ) :
    (∑ v, x v) ^ 2 = ∑ v, x v ^ 2 + 2 * ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) := by sorry
