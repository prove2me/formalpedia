-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_eq_gaussian_of_fderiv_add_eq_zero
-- name    : GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:09.439687+00:00
-- url     : https://prove2.me/theorems/c51ecefb-0fb7-4d4c-86a2-ac2d7c86fbd1
-- title:
--   Global Theory: schwartz eq gaussian of fderiv add eq zero
-- statement:
--   The Global Theory construction uses the schwartz eq gaussian of fderiv add eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqGaussianOfFderivAddEqZero.lean#L6-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqGaussianOfFderivAddEqZero.lean#L6-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqGaussianOfFderivAddEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory

theorem GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by sorry
