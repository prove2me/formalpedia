-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_tail_addMonoidHom_sixteen
-- name    : GlobalTheory.gaussian_tail_addMonoidHom_sixteen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:48.786343+00:00
-- url     : https://prove2.me/theorems/707f329d-8ef9-4019-a32c-00d4af30fc36
-- title:
--   Global Theory: gaussian tail add Monoid Hom sixteen
-- statement:
--   The Global Theory construction uses the gaussian tail add Monoid Hom sixteen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L137-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L137-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.gaussian_tail_addMonoidHom_sixteen {A : Type*} [AddGroup A] (u : A →+ E) {g : ℕ}
    (hg : finrank ℝ E = 2 * g) {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hu : ∀ y, y ≠ 0 → R ≤ ‖u y‖) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-‖u y‖ ^ 2 / 16)) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-‖u y‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) := by sorry
