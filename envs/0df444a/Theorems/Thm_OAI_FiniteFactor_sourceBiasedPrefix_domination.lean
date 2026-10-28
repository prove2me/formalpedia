-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceBiasedPrefix_domination
-- name    : OAI.FiniteFactor.sourceBiasedPrefix_domination
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:30:50.409373+00:00
-- url     : https://prove2.me/theorems/2ea394e4-ed5f-4c3c-91cb-e6b246128d38
-- title:
--   OAI.FiniteFactor.sourceBiasedPrefix_domination: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceBiasedPrefix_domination` of [lean/OAI/Analysis/FiniteFactor/BiasedPairs/PrefixDomination.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/BiasedPairs/PrefixDomination.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter ProbabilityTheory CouplingParameters Finset`, `open scoped ENNReal`):
--
--   ```lean
--   theorem sourceBiasedPrefix_domination (j n : ℕ) :
--       (sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus) ≪
--         ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
--           (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.SourceSamplingTorus`, `OAI.FiniteFactor.sourceBiasedPrefixMask`, `OAI.FiniteFactor.sourceBiasedTorusMeasure`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceSamplingLambdaTorus`, `OAI.FiniteFactor.CouplingParameters.BlockCoordinate` and `OAI.FiniteFactor.CouplingParameters.blockPrefix` (definitions bundle `OAIQ3Ff000` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.sourceProjection_biased_prefix_pairs` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/BiasedPairs/PrefixDomination.lean (declaration OAI.FiniteFactor.sourceBiasedPrefix_domination)

import Mathlib
import Definitions.Def_OAIQ3Ff000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

theorem sourceBiasedPrefix_domination (j n : ℕ) :
    (sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus) ≪
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
        (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus) := by
  sorry

end
end FiniteFactor

end OAI
end
