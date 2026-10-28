-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_band_coboundary_q44
-- name    : OAI.StandardMapEntropy.band_coboundary_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:14:33.434992+00:00
-- url     : https://prove2.me/theorems/45a575e2-b967-4b0a-ba9b-2f946841d15b
-- title:
--   OAI.StandardMapEntropy.band_coboundary_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.band_coboundary` of [lean/OAI/Dynamics/StandardMap/StandardMap/BandCoboundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BandCoboundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter MeasureTheory Topology`, `open scoped ENNReal Classical`):
--
--   ```lean
--   lemma band_coboundary_q44 (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
--       (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
--       (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (j:ℤ) :
--       (∫d,capG α (scaleZ j d).val ∂bandLaw μ)=bandMoment μ α (j+1)-bandMoment μ α j
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray` and `OAI.StandardMapEntropy.affineLocus` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.SlowShape`, `OAI.StandardMapEntropy.bandLaw`, `OAI.StandardMapEntropy.bandMoment`, `OAI.StandardMapEntropy.capG`, `OAI.StandardMapEntropy.nonaffineTranslation`, `OAI.StandardMapEntropy.realArray` and `OAI.StandardMapEntropy.scaleZ` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BandCoboundary.lean (declaration OAI.StandardMapEntropy.band_coboundary)

import Mathlib
import Definitions.Def_OAIQ44C002

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma band_coboundary_q44 (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (j:ℤ) :
    (∫d,capG α (scaleZ j d).val ∂bandLaw μ)=bandMoment μ α (j+1)-bandMoment μ α j := by
  sorry
end StandardMapEntropy

end OAI
end
