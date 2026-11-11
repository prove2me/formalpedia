-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_pack_length_bound_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:53.422682+00:00
-- url     : https://prove2.me/theorems/b1af35f8-c6f8-4e7f-9d07-a722fff7cedb
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopSize.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopSize.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop`, with `open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryCoupled (stateBits outcomeBits outputBits)`):
--
--   ```lean
--   lemma pack_length_bound_s238 {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
--       {total k h L precision : ℕ} {f : Frame (Fin m)} {base : List Bool} {b : ℚ}
--       (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3)
--       (hbase : base.length ≤ L) (hb : (BinaryRational.encode b).length ≤ L)
--       (hp : precision ≤ L) (hk : k.bits.length ≤ L) :
--       (pack base b precision k f).length ≤ capPoly.eval L
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.capPoly` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Valid` (definitions bundle `Q238K031` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopSize.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound)

import Mathlib
import Definitions.Def_Q238K031

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma pack_length_bound_s238 {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {total k h L precision : ℕ} {f : Frame (Fin m)} {base : List Bool} {b : ℚ}
    (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3)
    (hbase : base.length ≤ L) (hb : (BinaryRational.encode b).length ≤ L)
    (hp : precision ≤ L) (hk : k.bits.length ≤ L) :
    (pack base b precision k f).length ≤ capPoly.eval L := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end
