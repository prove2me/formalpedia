-- Prove2me | Theorems.Thm_OAI_RadialTransition_corePressure_uniform_bare_rt2
-- name    : OAI.RadialTransition.corePressure_uniform_bare_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:25.560588+00:00
-- url     : https://prove2.me/theorems/30e36c48-d948-4352-8926-3f0d778ea34d
-- title:
--   OAI.RadialTransition.corePressure_uniform_bare_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.corePressure_uniform_bare` of [lean/OAI/Probability/RadialTransition/CoreConvergence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/CoreConvergence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma corePressure_uniform_bare_rt2 {β₀ H ε : ℝ} (hβ₀ : 0 < β₀) (hH : 0 ≤ H) (hε : 0 < ε) :
--       ∀ᶠ t : ℝ in atTop, ∀ β h : ℝ, β₀ ≤ β → |h| ≤ H →
--         |grandPressure (corePotential t) t β h-bareLimit h| ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.bareLimit`, `OAI.RadialTransition.corePotential` and `OAI.RadialTransition.grandPressure` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.initial_separation_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/CoreConvergence.lean (declaration OAI.RadialTransition.corePressure_uniform_bare)

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

lemma corePressure_uniform_bare_rt2 {β₀ H ε : ℝ} (hβ₀ : 0 < β₀) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ β h : ℝ, β₀ ≤ β → |h| ≤ H →
      |grandPressure (corePotential t) t β h-bareLimit h| ≤ ε := by
  sorry

end RadialTransition
end

end OAI
end
