-- Prove2me | Theorems.Thm_OpenMath_WOWII96_conjecture96
-- name    : OpenMath.WOWII96.conjecture96
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:37:36.081948+00:00
-- url     : https://prove2.me/theorems/ad56f48c-8773-48bc-90fe-034eb126ac05
-- title:
--   WOWII96: conjecture96
-- statement:
--   **WOWII Conjecture 96** (statement verbatim from formal-conjectures).
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII96.lean#L209-L238
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII96.lean#L209-L238

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_OpenMath_WOWII96
set_option autoImplicit true
@[expose] public section
public section
open OpenMath OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [Nontrivial α]

theorem OpenMath.WOWII96.conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by sorry
