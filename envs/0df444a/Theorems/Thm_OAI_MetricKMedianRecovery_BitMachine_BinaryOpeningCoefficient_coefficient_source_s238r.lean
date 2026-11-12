-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningCoefficient_coefficient_source_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:50:30.305537+00:00
-- url     : https://prove2.me/theorems/d611a56d-41f1-4273-9bde-07778f9a2022
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/IfNat.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/IfNat.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient`, with `open WordOperations BinaryArithmetic`, `open WordList RationalLinearFeasibility RationalOpenability`):
--
--   ```lean
--   lemma coefficient_source_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
--       (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
--       coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
--         BinaryOpeningConstant.kindWord r),variableWord u))=
--         (EffectiveOpenability.forms distances F W v z lam eta i r).coeff u
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalOpenability.Kind`, `OAI.MetricKMedianRecovery.RationalOpenability.Variables` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Form` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.forms` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.variableWord` and `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.kindWord` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/IfNat.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

lemma coefficient_source_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
      BinaryOpeningConstant.kindWord r),variableWord u))=
      (EffectiveOpenability.forms distances F W v z lam eta i r).coeff u := by
  sorry
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end
