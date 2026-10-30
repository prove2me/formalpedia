-- Prove2me | Theorems.Thm_OAI_RadialTransition_initial_separation_rt2
-- name    : OAI.RadialTransition.initial_separation_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:36:13.749781+00:00
-- url     : https://prove2.me/theorems/24e6285f-745b-47b6-8f0a-d44df23229ff
-- title:
--   OAI.RadialTransition.initial_separation_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.initial_separation` of [lean/OAI/Probability/RadialTransition/InitialSeparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InitialSeparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma initial_separation_rt2 {τ ε₀ : ℝ} (hτ : 0 < τ) (hε₀ : 0 < ε₀) :
--       ∀ᶠ t : ℝ in atTop, ∀ x ∈ phaseWindow (1/4),
--         |onParameters (idealAttraction (grandPressure (corePotential t) t) phaseMass) x-
--           onParameters threePlane x| ≤ ε₀ ∧
--         HasPhaseGroups (idealAttraction (grandPressure (corePotential t) t) phaseMass) x (τ/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.HasPhaseGroups`, `OAI.RadialTransition.Parameter`, `OAI.RadialTransition.corePotential`, `OAI.RadialTransition.grandPressure`, `OAI.RadialTransition.idealAttraction`, `OAI.RadialTransition.onParameters`, `OAI.RadialTransition.phaseMass`, `OAI.RadialTransition.phaseWindow` and `OAI.RadialTransition.threePlane` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.exists_family_pressure_ball_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InitialSeparation.lean (declaration OAI.RadialTransition.initial_separation)

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

lemma initial_separation_rt2 {τ ε₀ : ℝ} (hτ : 0 < τ) (hε₀ : 0 < ε₀) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ phaseWindow (1/4),
      |onParameters (idealAttraction (grandPressure (corePotential t) t) phaseMass) x-
        onParameters threePlane x| ≤ ε₀ ∧
      HasPhaseGroups (idealAttraction (grandPressure (corePotential t) t) phaseMass) x (τ/2) := by
  sorry

end RadialTransition
end

end OAI
end
