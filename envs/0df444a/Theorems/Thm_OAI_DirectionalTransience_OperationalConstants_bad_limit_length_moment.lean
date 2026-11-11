-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_limit_length_moment
-- name    : OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:08.412277+00:00
-- url     : https://prove2.me/theorems/d194840d-1669-4ec4-beb7-3e4cfd0e806f
-- title:
--   OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment` of [lean/OAI/Probability/Ballisticity/Estimates/OperationalLengthMarks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/OperationalLengthMarks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Classical Topology`):
--
--   ```lean
--   lemma bad_limit_length_moment (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
--       (hD : 0≤D) (Ns : ℕ → ℕ)
--       (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
--       (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
--       (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
--       (ρ : ProbabilityMeasure (ActualEpisodeArray e))
--       (hlim : Tendsto (fun n => C.occupation hef (Ns n)
--         ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
--       (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).1<⊤) ∧
--         Integrable (fun Y => (logLengthMark e Y).toReal) (ρ : Measure (ActualEpisodeArray e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.HorizontalSpace`, `OAI.DirectionalTransience.horizontalOnePoint_measurable`, `OAI.DirectionalTransience.StationaryCompact.Label` and `OAI.DirectionalTransience.StationaryCompact.MarkSpace` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.OperationalConstants` and `OAI.DirectionalTransience.OperationalConstants.occupation` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.actualArray_borel`, `OAI.DirectionalTransience.badCrossingEvent` and `OAI.DirectionalTransience.logLengthMark` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row` and `OAI.DirectionalTransience.environmentLaw` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/OperationalLengthMarks.lean (declaration OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_length_moment (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).1<⊤) ∧
      Integrable (fun Y => (logLengthMark e Y).toReal) (ρ : Measure (ActualEpisodeArray e)) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
