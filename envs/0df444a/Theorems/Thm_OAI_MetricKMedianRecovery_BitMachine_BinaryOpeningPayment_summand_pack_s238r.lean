-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningPayment_summand_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:50:40.535976+00:00
-- url     : https://prove2.me/theorems/cd95b3c3-e1b1-4c18-a382-d99376fe0bbd
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment`, with `open WordOperations BinaryArithmetic`, `open WordList RationalLinearFeasibility`):
--
--   ```lean
--   lemma summand_pack_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
--       (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
--       summand (pairBits (pack distances F W v z lam eta i,j.val.bits))=
--         sourceSummand distances W v z i j
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sourceSummand` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

lemma summand_pack_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    summand (pairBits (pack distances F W v z lam eta i,j.val.bits))=
      sourceSummand distances W v z i j := by
  sorry

end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end
