-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_conditional_episode_drops
-- name    : OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:58.385249+00:00
-- url     : https://prove2.me/theorems/9d5f8537-a98d-4500-a001-127aba70c1fe
-- title:
--   OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops` of [lean/OAI/Probability/Ballisticity/Stationary/BadCrossingEpisodes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/BadCrossingEpisodes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory InformationTheory Filter`, `open scoped ENNReal NNReal Classical Topology`):
--
--   ```lean
--   theorem conditional_episode_drops [IsProbabilityMeasure ν]
--       (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
--       (N : ℕ) (hN : C.sfloor ≤ (N:ℝ)) (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
--       (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
--       (L : ℕ) (hL : 0<L) (hcharge : C.injectionCost ≤ 2*C.b*L) :
--       let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
--       (3/8*Real.log (N:ℝ) ≤ C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q)) ∧
--       ((∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) ≤ Real.log (N:ℝ)/(16*C.b)+1) ∧
--       (1/4*Real.log (N:ℝ) ≤ ∫ ω, ∑ i∈Finset.range N,
--         if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0 ∂Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.OperationalConstants`, `OAI.DirectionalTransience.OperationalConstants.activeCount`, `OAI.DirectionalTransience.OperationalConstants.dropAt`, `OAI.DirectionalTransience.OperationalConstants.injectionCost` and `OAI.DirectionalTransience.OperationalConstants.stagesAt` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.badCrossingEvent` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row` and `OAI.DirectionalTransience.environmentLaw` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks`, `OAI.DirectionalTransience.OperationalConstants.bad_dropMarkCut_upper`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_drop_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_occupation_stationary_limit` and `OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/BadCrossingEpisodes.lean (declaration OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops)

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

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} {e f : Direction d} {D : ℝ}

theorem conditional_episode_drops [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ)) (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (L : ℕ) (hL : 0<L) (hcharge : C.injectionCost ≤ 2*C.b*L) :
    let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
    (3/8*Real.log (N:ℝ) ≤ C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q)) ∧
    ((∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) ≤ Real.log (N:ℝ)/(16*C.b)+1) ∧
    (1/4*Real.log (N:ℝ) ≤ ∫ ω, ∑ i∈Finset.range N,
      if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0 ∂Q) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
