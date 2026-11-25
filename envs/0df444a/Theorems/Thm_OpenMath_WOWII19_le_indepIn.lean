-- Prove2me | Theorems.Thm_OpenMath_WOWII19_le_indepIn
-- name    : OpenMath.WOWII19.le_indepIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:16.246621+00:00
-- url     : https://prove2.me/theorems/423992db-3cc5-4c4b-8bf9-bdcdcfbf10a8
-- title:
--   WOWII19: le indep In
-- statement:
--   The WOWII19 construction uses the le indep In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L64-L70
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L64-L70

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

theorem OpenMath.WOWII19.le_indepIn {G : SimpleGraph α} {T s : Finset α} (hsT : s ⊆ T)
    (hs : (s : Set α).Pairwise fun x y => ¬ G.Adj x y) : s.card ≤ indepIn G T := by sorry
