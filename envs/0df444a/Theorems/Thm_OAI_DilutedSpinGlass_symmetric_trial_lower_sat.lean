-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_symmetric_trial_lower_sat
-- name    : OAI.DilutedSpinGlass.symmetric_trial_lower_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:24.084604+00:00
-- url     : https://prove2.me/theorems/8c36faac-6bfb-492a-b62c-339a3b382282
-- title:
--   OAI.DilutedSpinGlass.symmetric_trial_lower_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.symmetric_trial_lower` of [lean/OAI/Probability/DilutedSpin/SymmetricTrialLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/SymmetricTrialLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass`, with `open _root_.MeasureTheory ProbabilityTheory Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma symmetric_trial_lower_sat {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
--       (hθ : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
--       (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
--       (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
--         (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
--         functional M r ζ m ≤ liminf (pressure M) atTop+ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Exponents`, `OAI.DilutedSpinGlass.Hierarchy`, `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model`, `OAI.DilutedSpinGlass.Spin`, `OAI.DilutedSpinGlass.functional` and `OAI.DilutedSpinGlass.pressure` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat`, `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat` and `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/SymmetricTrialLower.lean (declaration OAI.DilutedSpinGlass.symmetric_trial_lower)

import Mathlib
import Definitions.Def_DilutedSpin

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

lemma symmetric_trial_lower_sat {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
    (hθ : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  sorry
end DilutedSpinGlass

end

end OAI
end
