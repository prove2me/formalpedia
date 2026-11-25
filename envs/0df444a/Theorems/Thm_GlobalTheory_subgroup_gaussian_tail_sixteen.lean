-- Prove2me | Theorems.Thm_GlobalTheory_subgroup_gaussian_tail_sixteen
-- name    : GlobalTheory.subgroup_gaussian_tail_sixteen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:26.146439+00:00
-- url     : https://prove2.me/theorems/d8bf8248-92c9-4dc8-af4b-bd17df0d4a39
-- title:
--   Global Theory: subgroup gaussian tail sixteen
-- statement:
--   The Global Theory construction uses the subgroup gaussian tail sixteen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L202-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L202-L208

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

theorem GlobalTheory.subgroup_gaussian_tail_sixteen (G : AddSubgroup E) {g : ℕ} (hg : finrank ℝ E = 2 * g)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hG : ∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) :
    Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
      ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) := by sorry
