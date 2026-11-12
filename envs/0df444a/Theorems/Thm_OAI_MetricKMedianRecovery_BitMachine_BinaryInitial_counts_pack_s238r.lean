-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_counts_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:10:05.428171+00:00
-- url     : https://prove2.me/theorems/d54ca5a5-d915-40af-a50f-782e636538e8
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryCoupled (stateBits outputBits outcomeBits)`):
--
--   ```lean
--   lemma counts_pack_s238r : lowerCount xx=(initialCount loc distance F v II.1 total).bits ∧
--       upperCount xx=(initialCount loc distance F v II.2 total).bits
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.PriceBisection.iterations` and `OAI.MetricKMedianRecovery.PriceBisection.search` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialCount` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.pack` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerCount` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperCount` (definitions bundle `Q238L043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack)

import Mathlib
import Definitions.Def_Q238L043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits outcomeBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryBisection.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ)
local notation "xx" => pack distance loc F v lo M N precision total k
local notation "II" => PriceBisection.search (fun lam=>initialCount loc distance F v lam total) k
    (PriceBisection.iterations lo (8*(d:ℚ)*M) precision) (lo,8*(d:ℚ)*M)
lemma counts_pack_s238r : lowerCount xx=(initialCount loc distance F v II.1 total).bits ∧
    upperCount xx=(initialCount loc distance F v II.2 total).bits := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end
