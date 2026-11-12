-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySensitive_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:24.617089+00:00
-- url     : https://prove2.me/theorems/674e77a4-bb8b-45c4-ac29-eddfe7988c0d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/SensitiveMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SensitiveMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
--       (F : Finset (Fin m)) (Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
--       (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
--       run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N H T U J)=
--         BinaryLengthSearch.resultBits (CanonicalSensitiveEndpoint.run loc distance F Q v lam b q n k key N H T U J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.run` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthSearch.resultBits` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run` (definitions bundle `Q238L043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SensitiveMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack)

import Mathlib
import Definitions.Def_Q238L043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma run_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N H T U J)=
      BinaryLengthSearch.resultBits (CanonicalSensitiveEndpoint.run loc distance F Q v lam b q n k key N H T U J) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end
