-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_tail_sums
-- name    : GlobalTheory.gaussian_tail_sums
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:16.861876+00:00
-- url     : https://prove2.me/theorems/9084e0a7-15b8-4e51-878a-ebae2b3e9874
-- title:
--   Global Theory: gaussian tail sums
-- statement:
--   The Global Theory construction uses the gaussian tail sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L238-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L238-L256

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

theorem GlobalTheory.gaussian_tail_sums :
    (∀ (G : AddSubgroup E) (g : ℕ) (R : ℝ), finrank ℝ E = 2 * g → 0 ≤ R →
      16 * (2 * (g : ℝ) + 1) ≤ R ^ 2 → (∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) →
      Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
        ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16)) ∧
    (∀ (S : Set E) (w : E), 1 ≤ finrank ℝ E → (S.Pairwise fun a b => 1 ≤ dist a b) →
      (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
      (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
          2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2)))) ∧
    (∀ (G : AddSubgroup E) (b q : ℝ), 0 < b → (finrank ℝ E : ℝ) + 1 ≤ q * b →
      (∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) →
      Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
        ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
          2 * 4.3 ^ finrank ℝ E * exp (-(q * b))) := by sorry
