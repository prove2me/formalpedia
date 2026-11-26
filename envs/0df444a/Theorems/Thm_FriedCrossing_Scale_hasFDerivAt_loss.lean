-- Prove2me | Theorems.Thm_FriedCrossing_Scale_hasFDerivAt_loss
-- name    : FriedCrossing.Scale.hasFDerivAt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:09.900691+00:00
-- url     : https://prove2.me/theorems/3536e866-ced6-4da6-b672-a96a203acfae
-- title:
--   Scale: has FDeriv At loss
-- statement:
--   THE DERIVATIVE WITH LOSS. For a ≥ b + 2 the family x ↦ incl a b ∘ R a x is Fréchet
--   differentiable with derivative `derivLoss`. Proof: the identity gives the difference as a product;
--   subtracting the candidate derivative leaves (loss-one Lipschitz) × O(h) = O(h²) plus (bounded) × o(h).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L165-L229
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L165-L229

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

theorem FriedCrossing.Scale.hasFDerivAt_loss (a b : ℕ) (hab : b + 2 ≤ a) (x₀ : X) :
    HasFDerivAt (fun x => (S.incl a b (by omega)).comp (F.R a x)) (derivLoss F a b hab x₀) x₀ := by sorry
