-- Prove2me | Theorems.Thm_GlobalTheory_GaussComplexForm_exists_schwartz_cexp_neg_form
-- name    : GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:07.466146+00:00
-- url     : https://prove2.me/theorems/d9241ec7-2853-4022-92f9-7c07b19be8ed
-- title:
--   Gauss Complex Form: exists schwartz cexp neg form
-- statement:
--   The Gauss Complex Form construction uses the exists schwartz cexp neg form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzCexpNegForm.lean#L7-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzCexpNegForm.lean#L7-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzCexpNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix Nat
open GlobalTheory GlobalTheory.GaussComplexForm

theorem GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by sorry
