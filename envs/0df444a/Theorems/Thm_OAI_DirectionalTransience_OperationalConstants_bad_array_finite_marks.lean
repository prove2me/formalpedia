-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_array_finite_marks
-- name    : OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:37.334603+00:00
-- url     : https://prove2.me/theorems/d260f750-1d70-4494-9cb8-7adaf5ad8322
-- title:
--   OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks` of [lean/OAI/Probability/Ballisticity/Stationary/BadFiniteArray.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/BadFiniteArray.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Classical Topology`):
--
--   ```lean
--   theorem bad_array_finite_marks (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
--       (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
--       (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
--       (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
--       (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
--       ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
--         StrictMono φ ∧
--         Tendsto (fun n => C.occupation hef (Ns (φ n))
--           ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
--         MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
--           (ρ : Measure (ActualEpisodeArray e)) ∧
--         (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
--           Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
--         (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
--           arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) ∧
--         (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
--           0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) ∧
--         Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
--         Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (ρ : Measure (ActualEpisodeArray e)) ∧
--         Integrable (fun Y => (Y.1 0).2.2.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
--         C.b ≤ ∫ Y, (Y.1 0).2.2.toReal ∂(ρ : Measure (ActualEpisodeArray e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.HorizontalSpace`, `OAI.DirectionalTransience.horizontalOnePoint_measurable`, `OAI.DirectionalTransience.StationaryCompact.EpisodeArray`, `OAI.DirectionalTransience.StationaryCompact.Label`, `OAI.DirectionalTransience.StationaryCompact.MarkSpace` and `OAI.DirectionalTransience.StationaryCompact.shift` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.OperationalConstants` and `OAI.DirectionalTransience.OperationalConstants.occupation` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.actualArray_borel`, `OAI.DirectionalTransience.arrayOffsetTest`, `OAI.DirectionalTransience.arrayProfileTest`, `OAI.DirectionalTransience.arraySamplingError` and `OAI.DirectionalTransience.badCrossingEvent` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row` and `OAI.DirectionalTransience.environmentLaw` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/BadFiniteArray.lean (declaration OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks)

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

theorem bad_array_finite_marks (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
        Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
        arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
        0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) ∧
      Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => (Y.1 0).2.2.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      C.b ≤ ∫ Y, (Y.1 0).2.2.toReal ∂(ρ : Measure (ActualEpisodeArray e)) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
