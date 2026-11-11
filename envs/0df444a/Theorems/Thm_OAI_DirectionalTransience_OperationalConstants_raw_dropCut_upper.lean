-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_raw_dropCut_upper
-- name    : OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:09.287773+00:00
-- url     : https://prove2.me/theorems/f9d40253-06ed-4d0f-a53d-7806bc575266
-- title:
--   OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper` of [lean/OAI/Probability/Ballisticity/Estimates/RawDropBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/RawDropBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Classical Topology`):
--
--   ```lean
--   lemma raw_dropCut_upper (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
--       (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
--       (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u) (B : ℝ≥0) :
--       (∫ Y, dropMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
--         (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
--         N (C.activeCount hef N)) ≤
--         C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) +
--         2*C.b*(∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
--           C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.HorizontalSpace`, `OAI.DirectionalTransience.horizontalOnePoint_measurable`, `OAI.DirectionalTransience.StationaryCompact.Label` and `OAI.DirectionalTransience.StationaryCompact.MarkSpace` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.OperationalConstants`, `OAI.DirectionalTransience.actualOccupationRaw`, `OAI.DirectionalTransience.episodeScaleRadius`, `OAI.DirectionalTransience.EpisodeChainLedger.steps`, `OAI.DirectionalTransience.OperationalConstants.activeCount`, `OAI.DirectionalTransience.OperationalConstants.injectionCost`, `OAI.DirectionalTransience.OperationalConstants.paddedStages`, `OAI.DirectionalTransience.OperationalConstants.paddedTimes`, `OAI.DirectionalTransience.OperationalConstants.paddedTimes_measurable` and `OAI.DirectionalTransience.OperationalConstants.radius_nonneg` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.dropMarkCut` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice` and `OAI.DirectionalTransience.Row` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.bad_dropMarkCut_upper` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/RawDropBounds.lean (declaration OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper)

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

lemma raw_dropCut_upper (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u) (B : ℝ≥0) :
    (∫ Y, dropMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) ≤
      C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) +
      2*C.b*(∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
