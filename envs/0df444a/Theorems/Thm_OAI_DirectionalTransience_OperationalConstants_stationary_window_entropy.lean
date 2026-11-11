-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_stationary_window_entropy
-- name    : OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:41.582377+00:00
-- url     : https://prove2.me/theorems/320d80b2-0179-4d08-8481-3b5a285ec580
-- title:
--   OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy` of [lean/OAI/Probability/Ballisticity/Stationary/StationaryWindowEntropy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/StationaryWindowEntropy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory InformationTheory Filter`, `open scoped ENNReal NNReal Classical Topology`):
--
--   ```lean
--   theorem stationary_window_entropy (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
--       (Ns : ℕ → ℕ)
--       (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
--       (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
--       (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
--       (ρ : ProbabilityMeasure (ActualEpisodeArray e))
--       (hlim : Tendsto (fun n => C.occupation hef (Ns n)
--         ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ))
--       (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
--         (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) (m : ℕ) :
--       let W := (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
--       klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
--         ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.CurrentProfiles`, `OAI.DirectionalTransience.CurrentWindow`, `OAI.DirectionalTransience.HorizontalSpace`, `OAI.DirectionalTransience.horizontalOnePoint_measurable`, `OAI.DirectionalTransience.ReferenceClasses.AllFields`, `OAI.DirectionalTransience.ReferenceClasses.Consistent`, `OAI.DirectionalTransience.ReferenceClasses.Data`, `OAI.DirectionalTransience.ReferenceClasses.Offsets`, `OAI.DirectionalTransience.ReferenceClasses.Site`, `OAI.DirectionalTransience.StationaryCompact.EpisodeArray`, `OAI.DirectionalTransience.StationaryCompact.Label`, `OAI.DirectionalTransience.StationaryCompact.MarkSpace` and `OAI.DirectionalTransience.StationaryCompact.shift` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.OperationalConstants`, `OAI.DirectionalTransience.OperationalConstants.occupation` and `OAI.DirectionalTransience.OperationalConstants.windowEntropyConstant` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.actualArray_borel` and `OAI.DirectionalTransience.badCrossingEvent` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.currentWindowReference` and `OAI.DirectionalTransience.typedCurrentArrayWindow` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row` and `OAI.DirectionalTransience.environmentLaw` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/StationaryWindowEntropy.lean (declaration OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
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
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

theorem stationary_window_entropy (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ))
    (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
      (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) (m : ℕ) :
    let W := (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
