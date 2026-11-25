-- Prove2me | Theorems.Thm_GrahamPollak_sum_prod_eq
-- name    : GrahamPollak.sum_prod_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:49.548855+00:00
-- url     : https://prove2.me/theorems/80d431d1-9389-4a33-b1e3-5b2057eb6911
-- title:
--   Graham Pollak: sum prod eq
-- statement:
--   The Graham Pollak construction uses the sum prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L68-L81
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean#L68-L81

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]

theorem GrahamPollak.sum_prod_eq [Fintype V] {m : ℕ} (A B : Fin m → Finset V) (x : V → ℝ) :
    ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) =
      ∑ u, ∑ v, x u * x v * ∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ)) := by sorry
