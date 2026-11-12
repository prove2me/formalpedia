-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_rowCoefficients_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:52:30.456443+00:00
-- url     : https://prove2.me/theorems/dfa48b7d-6ae5-4f36-8319-dc43ba04df1e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening`, with `open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability`, `open BinaryOpeningPayment BinaryOpeningEnumeration`):
--
--   ```lean
--   lemma rowCoefficients_pack_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
--       (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) :
--       rowCoefficients (pairBits (pack distances F W v z lam eta i,BinaryOpeningConstant.kindWord r))=
--         RationalMatrix.rowEncode (fun j=>(forms distances F W v z lam eta i r).coeff (variableEnum d F j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.EffectiveOpenability.variableEnum`, `OAI.MetricKMedianRecovery.RationalOpenability.Kind`, `OAI.MetricKMedianRecovery.RationalOpenability.Variables` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Form` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.forms` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.kindWord` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.rowEncode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack)

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

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
lemma rowCoefficients_pack_s238r {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) :
    rowCoefficients (pairBits (pack distances F W v z lam eta i,BinaryOpeningConstant.kindWord r))=
      RationalMatrix.rowEncode (fun j=>(forms distances F W v z lam eta i r).coeff (variableEnum d F j)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

end OAI
end
