-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalization_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:50:33.386915+00:00
-- url     : https://prove2.me/theorems/1bd7f732-56bf-4fc8-aa07-a74e7f6f0ea6
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_encode)`, `open IntegralAssembly (gammaRat)`):
--
--   ```lean
--   lemma run_pack_s238r {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
--       run (pack δ d M)=RationalMatrix.encode
--         (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate δ) ((gammaRat/16)*M/d)
--           (Rounding.cap d (IntegralAssembly.gamma/16)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.duplicate` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.round` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` and `OAI.MetricKMedianRecovery.IntegralAssembly.gammaRat` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.encode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack)

import Mathlib
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open IntegralAssembly (gammaRat)
lemma run_pack_s238r {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    run (pack δ d M)=RationalMatrix.encode
      (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate δ) ((gammaRat/16)*M/d)
        (Rounding.cap d (IntegralAssembly.gamma/16))) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end
