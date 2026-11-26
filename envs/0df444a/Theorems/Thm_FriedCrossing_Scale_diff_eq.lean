-- Prove2me | Theorems.Thm_FriedCrossing_Scale_diff_eq
-- name    : FriedCrossing.Scale.diff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:37:44.619298+00:00
-- url     : https://prove2.me/theorems/280550cd-45ed-588b-8d32-78f40def7fc5
-- title:
--   Scale: diff eq
-- statement:
--   incl a b ∘ (R a x − R a x₀) = (incl (b+1) b ∘ R (b+1) x) ∘ (B (b+1) x₀ − B (b+1) x) ∘
--   (incl a (b+2) ∘ R a x₀): the identity at level b+1, pushed through the inclusions.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L148-L160
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L148-L160

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)

theorem FriedCrossing.Scale.diff_eq (a b : ℕ) (hab : b + 2 ≤ a) (x x₀ : X) :
    (S.incl a b (by omega)).comp (F.R a x - F.R a x₀) =
      (((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        (F.B (b + 1) x₀ - F.B (b + 1) x)).comp ((S.incl a (b + 2) hab).comp (F.R a x₀)) := by sorry
