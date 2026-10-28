-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_bandMoment_order_q3
-- name    : OAI.StandardMapEntropy.bandMoment_order_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:48:10.681556+00:00
-- url     : https://prove2.me/theorems/6e3d37f8-760a-4e90-8eaf-02b4c20c2261
-- title:
--   OAI.StandardMapEntropy.bandMoment_order_q3: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy_complete`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.bandMoment_order` of [lean/OAI/Dynamics/StandardMap/StandardMap/BandComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BandComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter MeasureTheory Topology`, `open scoped ENNReal Classical`):
--
--   ```lean
--   lemma bandMoment_order_q3 (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
--       (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
--       (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
--       (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
--       {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
--       ∀ᶠn:ℕ in atTop, bandMoment μ α (n:ℤ)≤bandMoment μ α (-(n:ℤ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NoFastCancellation`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.SlowShape`, `OAI.StandardMapEntropy.TreeArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.bandMoment`, `OAI.StandardMapEntropy.nonaffineTranslation` and `OAI.StandardMapEntropy.realArray` (definitions bundle `OAIQ3St000` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q3` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BandComparison.lean (declaration OAI.StandardMapEntropy.bandMoment_order)

import Mathlib
import Definitions.Def_OAIQ3St000

section

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
lemma bandMoment_order_q3 (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    ∀ᶠn:ℕ in atTop, bandMoment μ α (n:ℤ)≤bandMoment μ α (-(n:ℤ)) := by
  sorry
end StandardMapEntropy

end OAI
end
