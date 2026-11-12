-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_atBranch_source_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:06:10.080201+00:00
-- url     : https://prove2.me/theorems/222ebd7c-36e9-4b21-9350-ac1ba3a6a3db
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryTape.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryTape.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery`, with `open WordOperations WordList BinaryBranchTape`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma atBranch_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
--       (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
--       (hn : n≤H) → (hm : m≤H) → (hp : s.leaves.length≤H) →
--       ∀ (q c : Fin (n+1)) (b : Fin m) (seed : Fin (tapeSize H)→Bool),
--       atBranch d (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),choiceBits q.val c.val b.val))=
--         let seed':=positiveSeed hn hm hp b seed
--         BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
--           (fun i=>ColorLabel.label (b.val+1) (by omega) (seed'.1.2 i)) q.val c.val r0 y0 seed'.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.ColorLabel.color`, `OAI.MetricKMedianRecovery.ColorLabel.label`, `OAI.MetricKMedianRecovery.ColorLabel.labelRange` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.tapeSize` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.Bits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.output` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.choiceBits` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.positiveSeed` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryTape.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] atBranch atZero context zeroContext
  BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout
lemma atBranch_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hp : s.leaves.length≤H) →
    ∀ (q c : Fin (n+1)) (b : Fin m) (seed : Fin (tapeSize H)→Bool),
    atBranch d (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),choiceBits q.val c.val b.val))=
      let seed':=positiveSeed hn hm hp b seed
      BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
        (fun i=>ColorLabel.label (b.val+1) (by omega) (seed'.1.2 i)) q.val c.val r0 y0 seed'.2) := by
  sorry

end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end
