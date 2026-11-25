-- Prove2me | Theorems.Thm_OpenMath_WOWII19_exists_indepIn
-- name    : OpenMath.WOWII19.exists_indepIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:24.923884+00:00
-- url     : https://prove2.me/theorems/5cbd7f80-ef65-4357-93bd-a106db07c8a2
-- title:
--   WOWII19: exists indep In
-- statement:
--   The WOWII19 construction uses the exists indep In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L72-L82
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L72-L82

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.WOWII19.exists_indepIn (G : SimpleGraph α) (T : Finset α) :
    ∃ s ⊆ T, (s : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧ s.card = indepIn G T := by sorry
