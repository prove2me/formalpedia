-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_finishes_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:11:42.67088+00:00
-- url     : https://prove2.me/theorems/8e54955a-5fe5-4962-8041-551da29ff3ef
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryCoupled (stateBits outputBits outcomeBits)`):
--
--   ```lean
--   lemma finishes_pack_s238 : lowerFinish xx=outputBits (finish ∅ II.1 [] (initialHistory loc distance F v II.1 total)) ∧
--       upperFinish xx=outputBits (finish ∅ II.2 [] (initialHistory loc distance F v II.2 total))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.PriceBisection.iterations` and `OAI.MetricKMedianRecovery.PriceBisection.search` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outputBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.finish`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialCount` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerFinish` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperFinish` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialPack.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack)

import Mathlib
import Definitions.Def_Q238K043

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
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ)
local notation "xx" => pack distance loc F v lo M N precision total k
local notation "II" => PriceBisection.search (fun lam=>initialCount loc distance F v lam total) k
    (PriceBisection.iterations lo (8*(d:ℚ)*M) precision) (lo,8*(d:ℚ)*M)
lemma finishes_pack_s238 : lowerFinish xx=outputBits (finish ∅ II.1 [] (initialHistory loc distance F v II.1 total)) ∧
    upperFinish xx=outputBits (finish ∅ II.2 [] (initialHistory loc distance F v II.2 total)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end
