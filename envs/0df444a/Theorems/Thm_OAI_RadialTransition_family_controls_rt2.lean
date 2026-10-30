-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_controls_rt2
-- name    : OAI.RadialTransition.family_controls_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:25.932438+00:00
-- url     : https://prove2.me/theorems/eb6945c3-4b3b-4368-9e43-4a7421c985f4
-- title:
--   OAI.RadialTransition.family_controls_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.family_controls` of [lean/OAI/Probability/RadialTransition/FamilyControls.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyControls.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma family_controls_rt2 {t A : ℝ} (ht : 1 ≤ t) (hA : 0 ≤ A) (htA : 6912*A ≤ t)
--       (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
--       ∃ U C C₀ : ℝ, 1 ≤ U ∧ 1 ≤ C ∧ 0 < C₀ ∧
--         ∀ b S : ℕ → ℝ, AdmissibleFamily t A b S → ∀ a ∈ Ioc (0:ℝ) A,
--         (∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (familyPotential t b S) t) a β h u) ∧
--         (∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U,
--           ActiveShift (grandPressure (familyPotential t b S) t) a (x 0) (x 1) u) ∧
--         (∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
--           |onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
--             onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) y| ≤ C*dist x y) ∧
--         (∀ x ∈ phaseWindow (1/4),
--           0 ≤ onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
--             onParameters (grandPressure (familyPotential t b S) t) x ∧
--           onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
--             onParameters (grandPressure (familyPotential t b S) t) x ≤ C₀*a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.ActiveShift`, `OAI.RadialTransition.AdmissibleFamily`, `OAI.RadialTransition.Parameter`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.grandPressure`, `OAI.RadialTransition.idealAttraction`, `OAI.RadialTransition.onParameters` and `OAI.RadialTransition.phaseWindow` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.exists_family_pressure_ball_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyControls.lean (declaration OAI.RadialTransition.family_controls)

import Mathlib
import Definitions.Def_OAIQ112R000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_controls_rt2 {t A : ℝ} (ht : 1 ≤ t) (hA : 0 ≤ A) (htA : 6912*A ≤ t)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    ∃ U C C₀ : ℝ, 1 ≤ U ∧ 1 ≤ C ∧ 0 < C₀ ∧
      ∀ b S : ℕ → ℝ, AdmissibleFamily t A b S → ∀ a ∈ Ioc (0:ℝ) A,
      (∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (familyPotential t b S) t) a β h u) ∧
      (∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U,
        ActiveShift (grandPressure (familyPotential t b S) t) a (x 0) (x 1) u) ∧
      (∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
        |onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) y| ≤ C*dist x y) ∧
      (∀ x ∈ phaseWindow (1/4),
        0 ≤ onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ∧
        onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ≤ C₀*a) := by
  sorry

end RadialTransition
end

end OAI
end
