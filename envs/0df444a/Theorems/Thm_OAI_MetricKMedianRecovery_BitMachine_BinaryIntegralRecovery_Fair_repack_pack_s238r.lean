-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_repack_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:58.89565+00:00
-- url     : https://prove2.me/theorems/74f34735-b4d8-4cdf-8853-b7eb0faa11fb
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySuccess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySuccess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair`, with `open WordOperations WordList Sampling.Comparison BinaryArithmetic`):
--
--   ```lean
--   lemma repack_pack_s238r (seed : Fin (count D Δ m)→Bool) :
--       repack (pack δ D F S Δ P m g (List.ofFn seed))=
--         BinaryIntegralRecovery.pack δ D F S Δ P m g (layout D Δ m seed).1 (List.ofFn (layout D Δ m seed).2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.tapeSize` and `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.layout` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySuccess.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack)

import Mathlib
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
include hm hΔ in
lemma repack_pack_s238r (seed : Fin (count D Δ m)→Bool) :
    repack (pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryIntegralRecovery.pack δ D F S Δ P m g (layout D Δ m seed).1 (List.ofFn (layout D Δ m seed).2) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end
