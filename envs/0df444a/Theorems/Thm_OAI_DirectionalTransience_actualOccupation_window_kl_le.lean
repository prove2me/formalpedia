-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actualOccupation_window_kl_le
-- name    : OAI.DirectionalTransience.actualOccupation_window_kl_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:23.24121+00:00
-- url     : https://prove2.me/theorems/a9647af1-81b7-48dd-8c16-5624bed6f5a4
-- title:
--   OAI.DirectionalTransience.actualOccupation_window_kl_le: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actualOccupation_window_kl_le` of [lean/OAI/Probability/Ballisticity/Entropy/WindowEntropy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Entropy/WindowEntropy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory InformationTheory`, `open scoped ENNReal Classical`):
--
--   ```lean
--   theorem actualOccupation_window_kl_le {d : ℕ} (e : Direction d)
--       (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
--       (hfin : klDiv Q (environmentLaw ν)≠∞)
--       (t J : Environment d → ℤ → ℕ)
--       (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
--       (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
--       (hmono : ∀ ω, Monotone (fun i : ℕ => t ω i))
--       (N m : ℕ) (M : Environment d → ℕ)
--       (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω)
--       (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
--       let W := (actualCurrentLaw e m (actualOccupation e ν Q t J ht N M) : Measure (CurrentWindow e))
--       klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
--         ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
--           (actualOccupationRaw e ν Q t J ht N M).real Set.univ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.BelowHeight`, `OAI.DirectionalTransience.CurrentProfiles`, `OAI.DirectionalTransience.CurrentWindow`, `OAI.DirectionalTransience.HorizontalSpace`, `OAI.DirectionalTransience.horizontalOnePoint_measurable`, `OAI.DirectionalTransience.rowSigma`, `OAI.DirectionalTransience.ReferenceClasses.AllFields`, `OAI.DirectionalTransience.ReferenceClasses.Consistent`, `OAI.DirectionalTransience.ReferenceClasses.Data`, `OAI.DirectionalTransience.ReferenceClasses.Offsets`, `OAI.DirectionalTransience.ReferenceClasses.Site`, `OAI.DirectionalTransience.StationaryCompact.Label` and `OAI.DirectionalTransience.StationaryCompact.MarkSpace` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.actualOccupation` and `OAI.DirectionalTransience.actualOccupationRaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.actualCurrentLaw` and `OAI.DirectionalTransience.currentWindowReference` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Entropy/WindowEntropy.lean (declaration OAI.DirectionalTransience.actualOccupation_window_kl_le)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem actualOccupation_window_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν)≠∞)
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (hmono : ∀ ω, Monotone (fun i : ℕ => t ω i))
    (N m : ℕ) (M : Environment d → ℕ)
    (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    let W := (actualCurrentLaw e m (actualOccupation e ν Q t J ht N M) : Measure (CurrentWindow e))
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (actualOccupationRaw e ν Q t J ht N M).real Set.univ) := by
  sorry

end DirectionalTransience

end

end OAI
end
