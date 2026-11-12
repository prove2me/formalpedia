-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Client_radii_pair_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:59:27.889832+00:00
-- url     : https://prove2.me/theorems/2f62673d-9d6d-4140-884d-e8b5478a4393
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerWeights.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerWeights.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma radii_pair_s238r (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
--       radii (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
--         BinaryMenu.radii κ (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) (RationalSampling.nearestLeaf δ s w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.distanceList` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.radiusQ` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalSampling.nearestLeaf` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.encode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.radii` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerWeights.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L035

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
lemma radii_pair_s238r (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    radii (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
      BinaryMenu.radii κ (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) (RationalSampling.nearestLeaf δ s w) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

end OAI
end
